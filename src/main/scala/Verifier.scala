package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import semper.silicon.decider.{PreambleFileEmitter, Z3ProverStdIO}
import scala.io.Source
import sil.verifier.errors.{ContractNotWellformed, PostconditionViolated, Internal, FunctionNotWellformed,
    PredicateNotWellformed}
import interfaces.{VerificationResult, Success, Producer, Consumer, Executor, Evaluator}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapMerger}
import state.{terms, SymbolConvert, DirectChunk}
import state.terms.{sorts, Sort, DefaultFractionalPermissions}
import interfaces.state.factoryUtils.Ø
import reporting.{DefaultContext, DefaultContextFactory, Bookkeeper}
import reporting.{DefaultHistory, Description}
import interfaces.reporting.{ContextFactory, TraceView}
import reporting.BranchingDescriptionStep
import interfaces.reporting.TraceViewFactory
import reporting.ScopeChangingDescription

trait AbstractElementVerifier[ST <: Store[ST],
														 H <: Heap[H], PC <: PathConditions[PC],
														 S <: State[ST, H, S],
														 TV <: TraceView[TV, ST, H, S]]
		extends Logging
		   with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Executor[ast.CFGBlock, ST, H, S, DefaultContext[ST, H, S], TV] {

	/*protected*/ val config: Config

  /*protected*/ val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]]
	import decider.{fresh, assume, inScope}

  /*protected*/ val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

  /*protected*/ val stateFormatter: StateFormatter[ST, H, S, String]
  /*protected*/ val symbolConverter: SymbolConvert

  /* Must be set when a program verification is started! */
  var program: ast.Program = null

  def contextFactory: ContextFactory[DefaultContext[ST, H, S], ST, H, S]
  def traceviewFactory: TraceViewFactory[TV, ST, H, S]

  def verify(member: ast.Member/*, history: History[ST, H, S]*/): VerificationResult = member match {
    case m: ast.Method => verify(m)
    case f: ast.ProgramFunction => verify(f)
    case p: ast.Predicate => verify(p)
    case _: ast.Domain | _: ast.Field =>
      val c = contextFactory.create(new DefaultHistory[ST, H, S]().tree)
      Success[DefaultContext[ST, H, S], ST, H, S](c)
  }

	def verify(method: ast.Method/*, history: History[ST, H, S]*/): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, method.name, "-" * 10))

    val ins = method.formalArgs.map(_.localVar)
    val outs = method.formalReturns.map(_.localVar)

    val history = new DefaultHistory[ST, H, S]()
    val c = contextFactory.create(history.tree)

    val tv = traceviewFactory.create(history)

    val γ = Γ(   ins.map(v => (v, fresh(v)))
              ++ outs.map(v => (v, fresh(v)))
              ++ method.locals.map(_.localVar).map(v => (v, fresh(v))))

    val σ = Σ(γ, Ø, Ø)

    val pres = method.pres
    val posts = method.posts
    val body = method.body.toCfg

    val postViolated = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, method)

		/* Combined the well-formedness check and the execution of the body, which are two separate
		 * rules in Smans' paper.
		 */
    inScope {
			produces(σ, fresh, terms.FullPerm(), pres, ContractNotWellformed, c, tv.stepInto(c, Description[ST, H, S]("Produce Precondition")))((σ1, c2) => {
				val σ2 = σ1 \ (γ = σ1.γ, h = Ø, g = σ1.h)
				val (c2a, tv0) = tv.splitOffLocally(c2, BranchingDescriptionStep[ST, H, S]("Check Postcondition well-formedness"))
			 (inScope {
         produces(σ2, fresh, terms.FullPerm(), posts, ContractNotWellformed, c2a, tv0)((_, c3) =>
           Success[DefaultContext[ST, H, S], ST, H, S](c3))}
					&&
        inScope {
          exec(σ1 \ (g = σ1.h), body, c2, tv.stepInto(c2, Description[ST, H, S]("Execute Body")))((σ2, c3) =>
            consumes(σ2, terms.FullPerm(), posts, postViolated, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Consume Postcondition")))((σ3, _, _, c4) =>
              Success[DefaultContext[ST, H, S], ST, H, S](c4)))})})}
	}

  def verify(function: ast.ProgramFunction/*, h: History[ST, H, S]*/): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " FUNCTION " + function.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, function.name, "-" * 10))

    val ins = function.formalArgs.map(_.localVar)
    val out = function.result

    val history = new DefaultHistory[ST, H, S]()
    val c = contextFactory.create(history.tree)
    val tv = traceviewFactory.create(history)

    val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
    val σ = Σ(γ, Ø, Ø)

    val postError = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, function)
    val malformedError = (_: ast.Expression) => FunctionNotWellformed(function)
    val internalError = (offendingNode: ast.Expression) => Internal(offendingNode)

    /* TODO:
     *  - Improve error message in case the ensures-clause is not well-defined
     */

    /* Produce includes well-formedness check */
    inScope {
      val (c0, tv0) = tv.splitOffLocally(c, BranchingDescriptionStep[ST, H, S]("Check Precondition & Postcondition well-formedness"))
      (inScope {
        produces(σ, fresh, terms.FullPerm(), function.pres ++ function.posts, malformedError, c0, tv0)((_, c2) =>
          Success[DefaultContext[ST, H, S], ST, H, S](c2))}
        &&
        inScope {
          produces(σ, fresh, terms.FullPerm(), function.pres, internalError, c, tv.stepInto(c, Description[ST, H, S]("Produce Precondition")))((σ1, c2) =>
            eval(σ1, function.exp, FunctionNotWellformed(function), c2, tv.stepInto(c2, Description[ST, H, S]("Execute Body")))((tB, c3) =>
              consumes(σ1 \+ (out, tB), terms.FullPerm(), function.posts, postError, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Consume Postcondition")))((_, _, _, c4) =>
                Success[DefaultContext[ST, H, S], ST, H, S](c4))))})}
  }

  def verify(predicate: ast.Predicate/*, h: History[ST, H, S]*/): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

    val history = new DefaultHistory[ST, H, S]()
    val c = contextFactory.create(history.tree)
    val tv = traceviewFactory.create(history)

//    val vThis = predicate.formalArg.localVar
//    val tThis = fresh(vThis)

//    val γ = Γ(vThis -> tThis)
//    val γ = Γ(vThis -> tThis)
    val σ = Σ(Ø, Ø, Ø)

    inScope {
//      assume(tThis !== terms.Null())
      produce(σ, fresh, terms.FullPerm(), predicate.body, PredicateNotWellformed(predicate), c, tv)((_, c1) =>
        Success[DefaultContext[ST, H, S], ST, H, S](c1))}
  }
}

class DefaultElementVerifier[ST <: Store[ST],
                             H <: Heap[H],
														 PC <: PathConditions[PC],
                             S <: State[ST, H, S],
                             TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
		  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
			val stateFactory: StateFactory[ST, H, S],
			val symbolConverter: SymbolConvert,
			val chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
			val stateFormatter: StateFormatter[ST, H, S, String],
			val heapMerger: HeapMerger[H],
      val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
			val bookkeeper: Bookkeeper,
			val contextFactory: ContextFactory[DefaultContext[ST, H, S], ST, H, S],
      val traceviewFactory: TraceViewFactory[TV, ST, H, S])
		extends AbstractElementVerifier[ST, H, PC, S, TV]
       with Logging
       with DefaultEvaluator[ST, H, PC, S, TV]
       with DefaultProducer[ST, H, PC, S, TV]
       with DefaultConsumer[ST, H, PC, S, TV]
       with DefaultExecutor[ST, H, PC, S, TV]
       with DefaultBrancher[ST, H, PC, S, DefaultContext[ST, H, S], TV]


trait VerifierFactory[V <: AbstractVerifier[ST, H, PC, S, TV],
                      TV <: TraceView[TV, ST, H, S],
                      ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]] {

  def create(config: Config,
             decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
             stateFactory: StateFactory[ST, H, S],
             symbolConverter: SymbolConvert,
             preambleEmitter: PreambleFileEmitter[_],
             sequenceEmitter: SequenceEmitter,
             domainEmitter: DomainEmitter,
             chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
             stateFormatter: StateFormatter[ST, H, S, String],
             heapMerger: HeapMerger[H],
             stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
             bookkeeper: Bookkeeper,
             traceviewFactory: TraceViewFactory[TV, ST, H, S]): V
}

trait AbstractVerifier[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
                       S <: State[ST, H, S],
                       TV <: TraceView[TV, ST, H, S]]
      extends Logging {

  /*protected*/ def decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]]
  /*protected*/ def config: Config
  /*protected*/ def bookkeeper: Bookkeeper
  /*protected*/ def preambleEmitter: PreambleFileEmitter[_]
  /*protected*/ def sequenceEmitter: SequenceEmitter
  /*protected*/ def domainEmitter: DomainEmitter

  val ev: AbstractElementVerifier[ST, H, PC, S, TV]
  import ev.symbolConverter

  def verify(program: ast.Program): List[VerificationResult] = {
    ev.program = program

    emitPreamble(program)

    val members = program.members.iterator

    /* Verification can be parallelised by forking DefaultMemberVerifiers. */
    var results: List[VerificationResult] = Nil

    if (config.stopOnFirstError) {
      /* Stops on first error */
      while (members.nonEmpty && (results.isEmpty || !results.head.isFatal)) {
        results = ev.verify(members.next) :: results
      }

      results = results.reverse
    } else {
      /* Verify members. Verification continues if errors are found, i.e.
       * all members are verified regardless of previous errors.
       * However, verification of a single member is aborted on first error.
       */
      results = members.map(ev.verify _).toList
    }

    results
  }

  private def emitPreamble(program: ast.Program) {
    sequenceEmitter.reset()
    sequenceEmitter.analyze(program)

    domainEmitter.reset()
    domainEmitter.analyze(program)

    decider.prover.logComment("Started: " + bookkeeper.formattedStartTime)
    decider.prover.logComment("Silicon.buildVersion: " + Silicon.buildVersion)

    decider.prover.logComment("-" * 60)
    decider.prover.logComment("Preamble start")

    emitStaticPreamble()

    sequenceEmitter.declareSorts()
    domainEmitter.declareSorts()

    sequenceEmitter.declareSymbols()
    domainEmitter.declareSymbols()
    domainEmitter.emitUniquenessAssumptions()

    sequenceEmitter.emitAxioms()
    domainEmitter.emitAxioms()

    emitSortWrappers(domainEmitter.sorts)
    emitSortWrappers(sequenceEmitter.sorts)

    decider.prover.logComment("Preamble end")
    decider.prover.logComment("-" * 60)

    emitProgramFunctionDeclarations(program.functions)
  }

  private def emitProgramFunctionDeclarations(fs: Seq[ast.ProgramFunction]) {
    fs foreach (f =>
      decider.prover.declare(terms.FunctionDecl(symbolConverter.toFunction(f))))
  }

  private def emitSortWrappers(ss: Set[Sort]) {
    decider.prover.logComment("")
    decider.prover.logComment("Declaring additional sort wrappers")
    decider.prover.logComment("")

    ss.foreach(sort => {
      val toSnapWrapper = terms.SortWrapperDecl(sort, sorts.Snap)
      val fromSnapWrapper = terms.SortWrapperDecl(sorts.Snap, sort)

      decider.prover.declare(toSnapWrapper)
      decider.prover.declare(fromSnapWrapper)
    })
  }

  private def emitStaticPreamble() {
    decider.prover.logComment("\n; /preamble.smt2")
    preambleEmitter.emitPreamble("/preamble.smt2")

    decider.pushScope()
  }
}

class DefaultVerifierFactory[ST <: Store[ST],
                             H <: Heap[H],
                             PC <: PathConditions[PC],
                             S <: State[ST, H, S],
                             TV <: TraceView[TV, ST, H, S]]
    extends VerifierFactory[DefaultVerifier[ST, H, PC, S, TV], TV, ST, H, PC, S] {

  def create(config: Config,
             decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
             stateFactory: StateFactory[ST, H, S],
             symbolConverter: SymbolConvert,
             preambleEmitter: PreambleFileEmitter[_],
             sequenceEmitter: SequenceEmitter,
             domainEmitter: DomainEmitter,
             chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
             stateFormatter: StateFormatter[ST, H, S, String],
             heapMerger: HeapMerger[H],
             stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
             bookkeeper: Bookkeeper,
             traceviewFactory: TraceViewFactory[TV, ST, H, S]) =

    new DefaultVerifier[ST, H, PC, S, TV](
                        config, decider, stateFactory, symbolConverter, preambleEmitter, sequenceEmitter, domainEmitter,
                        chunkFinder, stateFormatter, heapMerger, stateUtils, bookkeeper, traceviewFactory)

}

class DefaultVerifier[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC],
											S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
			val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
			val stateFactory: StateFactory[ST, H, S],
			val symbolConverter: SymbolConvert,
      val preambleEmitter: PreambleFileEmitter[_],
      val sequenceEmitter: SequenceEmitter,
			val domainEmitter: DomainEmitter,
			val chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
			val stateFormatter: StateFormatter[ST, H, S, String],
			val heapMerger: HeapMerger[H],
      val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
			val bookkeeper: Bookkeeper,
      val traceviewFactory: TraceViewFactory[TV, ST, H, S])
		extends AbstractVerifier[ST, H, PC, S, TV]
			 with Logging {

  val contextFactory = new DefaultContextFactory[ST, H, S]

	val ev = new DefaultElementVerifier(config, decider, stateFactory, symbolConverter, chunkFinder, stateFormatter,
                                      heapMerger, stateUtils, bookkeeper, contextFactory, traceviewFactory)
}
