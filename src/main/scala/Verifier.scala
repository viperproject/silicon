package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{ContractNotWellformed, PostconditionViolated, Internal, FunctionNotWellformed,
    PredicateNotWellformed}
import sil.components.StatefulComponent
import interfaces.{Evaluator, Producer, Consumer, Executor, VerificationResult, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapCompressor}
import interfaces.state.factoryUtils.Ø
import interfaces.reporting.{TraceView, TraceViewFactory}
import semper.silicon.state.{terms, SymbolConvert, DirectChunk}
import semper.silicon.state.terms.{sorts, Sort, DefaultFractionalPermissions}
import theories.{DomainsEmitter, SetsEmitter, MultisetsEmitter, SequencesEmitter}
import semper.silicon.reporting.{DefaultContext, Bookkeeper}
import semper.silicon.reporting.{DefaultHistory, Description, BranchingDescriptionStep, ScopeChangingDescription}
import heap.QuantifiedChunkHelper
import semper.silicon.decider.PreambleFileEmitter

trait AbstractElementVerifier[ST <: Store[ST],
														 H <: Heap[H], PC <: PathConditions[PC],
														 S <: State[ST, H, S],
														 TV <: TraceView[TV, ST, H, S]]
		extends Logging
		   with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Executor[ast.CFGBlock, ST, H, S, DefaultContext[ST, H, S], TV] {

  private type C = DefaultContext[ST, H, S]

	/*protected*/ val config: Config

  /*protected*/ val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]
	import decider.{fresh, inScope}

  /*protected*/ val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

  /*protected*/ val stateFormatter: StateFormatter[ST, H, S, String]
  /*protected*/ val symbolConverter: SymbolConvert

  def traceviewFactory: TraceViewFactory[TV, ST, H, S]

  def verify(program: ast.Program, member: ast.Member/*, history: History[ST, H, S]*/): VerificationResult = {
    val history = new DefaultHistory[ST, H, S]()
    val c = DefaultContext(program, history.tree)
    val tv = traceviewFactory.create(history)

    member match {
      case m: ast.Method => verify(m, c, tv)
      case f: ast.ProgramFunction => verify(f, c, tv)
      case p: ast.Predicate => verify(p, c, tv)
      case _: ast.Domain | _: ast.Field => Success()
    }
  }

	def verify(method: ast.Method, c: C, tv: TV): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, method.name, "-" * 10))

    val ins = method.formalArgs.map(_.localVar)
    val outs = method.formalReturns.map(_.localVar)

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
           Success())}
					&&
        inScope {
          exec(σ1 \ (g = σ1.h), body, c2, tv.stepInto(c2, Description[ST, H, S]("Execute Body")))((σ2, c3) =>
            consumes(σ2, terms.FullPerm(), posts, postViolated, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Consume Postcondition")))((σ3, _, _, c4) =>
              Success()))})})}
	}

  def verify(function: ast.ProgramFunction, c: C, tv: TV): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " FUNCTION " + function.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, function.name, "-" * 10))

    val ins = function.formalArgs.map(_.localVar)
    val out = function.result

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
          Success())}
        &&
        inScope {
          produces(σ, fresh, terms.FullPerm(), function.pres, internalError, c, tv.stepInto(c, Description[ST, H, S]("Produce Precondition")))((σ1, c2) =>
            eval(σ1, function.exp, FunctionNotWellformed(function), c2, tv.stepInto(c2, Description[ST, H, S]("Execute Body")))((tB, c3) =>
              consumes(σ1 \+ (out, tB), terms.FullPerm(), function.posts, postError, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Consume Postcondition")))((_, _, _, c4) =>
                Success())))})}
  }

  def verify(predicate: ast.Predicate, c: C, tv: TV): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

    val ins = predicate.formalArgs.map(_.localVar)

    val γ = Γ(ins.map(v => (v, fresh(v))))
    val σ = Σ(γ, Ø, Ø)

    inScope {
      produce(σ, fresh, terms.FullPerm(), predicate.body, PredicateNotWellformed(predicate), c, tv)((_, c1) =>
        Success())}
  }
}

class DefaultElementVerifier[ST <: Store[ST],
                             H <: Heap[H],
														 PC <: PathConditions[PC],
                             S <: State[ST, H, S],
                             TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
		  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S], TV],
			val stateFactory: StateFactory[ST, H, S],
			val symbolConverter: SymbolConvert,
			val stateFormatter: StateFormatter[ST, H, S, String],
			val heapCompressor: HeapCompressor[ST, H, S],
      val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, DefaultContext[ST, H, S], TV],
      val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S], TV],
			val bookkeeper: Bookkeeper,
      val traceviewFactory: TraceViewFactory[TV, ST, H, S])
		extends AbstractElementVerifier[ST, H, PC, S, TV]
       with DefaultEvaluator[ST, H, PC, S, TV]
       with DefaultProducer[ST, H, PC, S, TV]
       with DefaultConsumer[ST, H, PC, S, TV]
       with DefaultExecutor[ST, H, PC, S, TV]
       with DefaultBrancher[ST, H, PC, S, DefaultContext[ST, H, S], TV]
       with Logging

trait AbstractVerifier[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
                       S <: State[ST, H, S],
                       TV <: TraceView[TV, ST, H, S]]
    extends StatefulComponent
       with Logging {

  /*protected*/ def decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S], TV]
  /*protected*/ def config: Config
  /*protected*/ def bookkeeper: Bookkeeper
  /*protected*/ def preambleEmitter: PreambleFileEmitter[_]
  /*protected*/ def sequencesEmitter: SequencesEmitter
  /*protected*/ def setsEmitter: SetsEmitter
  /*protected*/ def multisetsEmitter: MultisetsEmitter
  /*protected*/ def domainsEmitter: DomainsEmitter

  val ev: AbstractElementVerifier[ST, H, PC, S, TV]
  import ev.symbolConverter

  private val statefulSubcomponents = List[StatefulComponent](
    bookkeeper,
    preambleEmitter, sequencesEmitter, setsEmitter, multisetsEmitter, domainsEmitter,
    decider)

  /* Lifetime */

  def start() { /* Nothing to be done here */ }

  def reset() {
    statefulSubcomponents foreach (_.reset())
  }

  def stop() {
    statefulSubcomponents foreach (_.stop())
  }

  /* Functionality */

  def verify(program: ast.Program): List[VerificationResult] = {
    emitPreamble(program)

    val members = program.members.filterNot(m => filter(m.name)).iterator
    var results: List[VerificationResult] = Nil

    /* Verification could be parallelised by forking DefaultMemberVerifiers. */

    if (config.stopOnFirstError()) {
      /* Stops on first error */
      while (members.nonEmpty && (results.isEmpty || !results.head.isFatal)) {
        results = ev.verify(program, members.next()) :: results
      }

      results = results.reverse
    } else {
      /* Verify members. Verification continues if errors are found, i.e.
       * all members are verified regardless of previous errors.
       * However, verification of a single member is aborted on first error.
       */
      results = members.map(m => ev.verify(program, m)).toList
    }

    results
  }

  private def filter(str: String) = (
       !str.matches(config.includeMembers())
    || str.matches(config.excludeMembers()))

  private def emitPreamble(program: ast.Program) {
    decider.prover.logComment("Started: " + bookkeeper.formattedStartTime)
    decider.prover.logComment("Silicon.buildVersion: " + Silicon.buildVersion)

    decider.prover.logComment("-" * 60)
    decider.prover.logComment("Preamble start")

    sequencesEmitter.analyze(program)
    setsEmitter.analyze(program)
    multisetsEmitter.analyze(program)
    domainsEmitter.analyze(program)

    emitStaticPreamble()

    sequencesEmitter.declareSorts()
    setsEmitter.declareSorts()
    multisetsEmitter.declareSorts()
    domainsEmitter.declareSorts()

    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     */
    setsEmitter.declareSymbols()
    multisetsEmitter.declareSymbols()
    sequencesEmitter.declareSymbols()
    domainsEmitter.declareSymbols()
    domainsEmitter.emitUniquenessAssumptions()

    sequencesEmitter.emitAxioms()
    setsEmitter.emitAxioms()
    multisetsEmitter.emitAxioms()
    domainsEmitter.emitAxioms()

    emitSortWrappers(Set(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm))
    emitSortWrappers(sequencesEmitter.sorts)
    emitSortWrappers(setsEmitter.sorts)
    emitSortWrappers(multisetsEmitter.sorts)
    emitSortWrappers(domainsEmitter.sorts)

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

      preambleEmitter.emitSortParametricAssertions("/sortwrappers.smt2", sort)
    })
  }

  private def emitStaticPreamble() {
    decider.prover.logComment("\n; /preamble.smt2")
    preambleEmitter.emitPreamble("/preamble.smt2")

    decider.pushScope()
  }
}

class DefaultVerifier[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
											S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
			val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S], TV],
			val stateFactory: StateFactory[ST, H, S],
			val symbolConverter: SymbolConvert,
      val preambleEmitter: PreambleFileEmitter[_],
      val sequencesEmitter: SequencesEmitter,
      val setsEmitter: SetsEmitter,
      val multisetsEmitter: MultisetsEmitter,
			val domainsEmitter: DomainsEmitter,
			val stateFormatter: StateFormatter[ST, H, S, String],
			val heapCompressor: HeapCompressor[ST, H, S],
      val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, DefaultContext[ST, H, S], TV],
      val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S], TV],
			val bookkeeper: Bookkeeper,
      val traceviewFactory: TraceViewFactory[TV, ST, H, S])
		extends AbstractVerifier[ST, H, PC, S, TV]
			 with Logging {

	val ev = new DefaultElementVerifier(config, decider, stateFactory, symbolConverter, stateFormatter, heapCompressor,
                                      quantifiedChunkHelper, stateUtils, bookkeeper, traceviewFactory)
}
