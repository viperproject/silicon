package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{AssertionMalformed, PostconditionViolated}
import interfaces.{VerificationResult, Success, Producer, Consumer, Executor, Evaluator}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
    HeapMerger}
import state.{terms, TypeConverter, DirectChunk}
import state.terms.{Term, PermissionsTuple/*, TypeOf*/}
import state.terms.implicits._
import interfaces.state.factoryUtils.Ø
//import ast.utils.collections.SetAnd
//import reporting.ErrorMessages.{ExecutionFailed, PostconditionMightNotHold, SpecsMalformed}
//import reporting.WarningMessages.{ExcludingUnit}
import reporting.{DefaultContext, DefaultContextFactory, Bookkeeper}
import reporting.{DefaultHistory, Description}
import interfaces.reporting.{ContextFactory, History, TraceView}
import reporting.BranchingDescriptionStep
import interfaces.reporting.TraceViewFactory
import reporting.ScopeChangingDescription

trait AbstractElementVerifier[ST <: Store[ST],
														 H <: Heap[H], PC <: PathConditions[PC],
														 S <: State[ST, H, S],
														 TV <: TraceView[TV, ST, H, S]]
		extends Logging
		   with Evaluator[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Producer[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Consumer[PermissionsTuple, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		   with Executor[ast.CFGBlock, ST, H, S, DefaultContext[ST, H, S], TV] {

	/*protected*/ val config: Config

  /*protected*/ val decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]]
	import decider.{fresh, assume, inScope}

  /*protected*/ val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

//  /*protected*/ val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]]
//  import stateUtils.freshReadVar

  /*protected*/ val typeConverter: TypeConverter
  import typeConverter.toSort

  def contextFactory: ContextFactory[DefaultContext[ST, H, S], ST, H, S]
  def traceviewFactory: TraceViewFactory[TV, ST, H, S]

	def verify(method: ast.Method/*, history: History[ST, H, S]*/): VerificationResult = {
    logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
    decider.prover.logComment("%s %s %s".format("-" * 10, method.name, "-" * 10))

    val ins = method.formalArgs.map(_.localVar)
    val outs = method.formalReturns.map(_.localVar)

//    val (rdVar, rdVarConstraints) = freshReadVar("$MethRd")

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
//		  assume(rdVarConstraints, c)
			produces(σ, fresh, terms.FullPerm(), pres, AssertionMalformed, c, tv.stepInto(c, Description[ST, H, S]("Produce Precondition")))((σ1, c2) => {
				val σ2 = σ1 \ (γ = σ1.γ, h = Ø, g = σ1.h)
				val (c2a, tv0) = tv.splitOffLocally(c2, BranchingDescriptionStep[ST, H, S]("Check Postcondition well-formedness"))
			 (inScope {
         produces(σ2, fresh, terms.FullPerm(), posts, AssertionMalformed, c2a, tv0)((_, c3) =>
           Success[DefaultContext[ST, H, S], ST, H, S](c3))}
					&&
        inScope {
          exec(σ1 \ (g = σ1.h), body, c2, tv.stepInto(c2, Description[ST, H, S]("Execute Body")))((σ2, c3) =>
            consumes(σ2, terms.FullPerm(), posts, postViolated, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Consume Postcondition")))((σ3, _, _, c4) =>
                Success[DefaultContext[ST, H, S], ST, H, S](c4)))})})}
	}
}

class DefaultElementVerifier[ST <: Store[ST],
                             H <: Heap[H],
														 PC <: PathConditions[PC],
                             S <: State[ST, H, S],
                             TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
		  val decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]],
			val stateFactory: StateFactory[ST, H, S],
			val typeConverter: TypeConverter,
			val chunkFinder: ChunkFinder[ST, H, S, DefaultContext[ST, H, S], TV],
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
      decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]],
      stateFactory: StateFactory[ST, H, S],
      typeConverter: TypeConverter,
      chunkFinder: ChunkFinder[ST, H, S, DefaultContext[ST, H, S], TV],
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

  def decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]]
  def config: Config
  def bookkeeper: Bookkeeper

  val ev: AbstractElementVerifier[ST, H, PC, S, TV]
  import ev.typeConverter

  def verify(prog: ast.Program): List[VerificationResult] = {
    emitDomainDeclarations(prog.domains)
    emitSortWrappers(prog.domains)
    emitFunctionDeclarations(prog.functions)

    var it: Iterator[ast.Method] = prog.methods.iterator

    /* Verification can be parallelised by forking DefaultMemberVerifiers. */
    var results: List[VerificationResult] = Nil

    if (config.stopOnFirstError) {
      /* Stops on first error */
      while (it.nonEmpty && (results.isEmpty || !results.head.isFatal)) {
        results = verify(it.next) :: results
      }

      results = results.reverse
    } else {
      /* Verify members. Verification continues if errors are found, i.e.
       * all members are verified regardless of previous errors.
       * However, verification of a single member is aborted on first error.
       */
      results = it.map(verify _).toList
    }

    results
  }

  def verify(method: ast.Method): VerificationResult = ev.verify(method)

  private def emitFunctionDeclarations(fs: Seq[ast.Function]) {
    fs.foreach(f => {
      var args: List[terms.Sort] = f.formalArgs.map(a => typeConverter.toSort(a.typ)).toList
      args = terms.sorts.Snap :: args /* Snapshot, and all declared parameters */
      decider.prover.declareSymbol(f.name, args, typeConverter.toSort(f.typ))
    })
  }

  private def emitSortWrappers(domains: Seq[ast.Domain]) {
    val snapSortId = decider.prover.termConverter.convert(terms.sorts.Snap)

    decider.prover.logComment("")
    decider.prover.logComment("Declaring additional sort wrappers")
    decider.prover.logComment("")

    domains.foreach(d => {
      val domainSort = typeConverter.toSort(ast.types.DomainType(d, Map.empty))
      val domainSortId = decider.prover.termConverter.convert(domainSort)
      val toSnapId = "$SortWrappers.%sTo%s".format(domainSortId, snapSortId)
      val fromSnapId = "$SortWrappers.%sTo%s".format(snapSortId, domainSortId)
      /* TODO: Sort wrapper naming schema must be the same as used by the
       *       TermConverter when converting SortWrapper(t, to) terms!!!
       */

      decider.prover.declareSymbol(toSnapId, Seq(domainSort), terms.sorts.Snap)
      decider.prover.declareSymbol(fromSnapId, Seq(terms.sorts.Snap), domainSort)
    })
  }

  private def emitDomainDeclarations(domains: Seq[ast.Domain]) {
    decider.prover.logComment("")
    decider.prover.logComment("Declaring additional domains")
    decider.prover.logComment("")

    /* Declare domains. */
    domains.foreach(d => {
      decider.prover.logComment("Declaring domain " + d.name)
      decider.prover.declareSort(typeConverter.toSort(ast.types.DomainType(d, Map.empty)))
    })

    /* Declare functions and predicates of each domain.
     * Since these can reference arbitrary other domains, make sure that
     * all domains have been declared first.
     */
    domains.foreach(d => {
      decider.prover.logComment("Functions of " + d.name)
      d.functions.foreach(f =>
        decider.prover.declareSymbol(f.name,
          f.formalArgs.map(a => typeConverter.toSort(a.typ)),
          typeConverter.toSort(f.typ)))
    })

    /* Axiomatise each domain.
     * Since the axioms can reference arbitrary domains, functions and
     * predicates, make sure that all domains, functions and predicates have
     * been declared first.
     *
     * TODO: Evaluating the domains is probably an overkill, because
     *         - domain axioms are much simpler than regular SIL expressions
     *         - we don't care about read permissions
     *         - we don't care about traceviews
     */
    domains.foreach(d => {
      decider.prover.logComment("Axiomatising domain " + d.name)
      decider.prover.logComment("Axioms (eval)")

//      val (rdVar, _) = ev.stateUtils.freshReadVar("$MethRd")
      val history = new DefaultHistory[ST, H, S]()
      val tv = ev.traceviewFactory.create(history)
      val c = ev.contextFactory.create(history.tree /*, terms.ReadPerm(rdVar)*/)

      val axioms =
        decider.inScope {
          d.axioms.map(a => {
            import ev.stateFactory._

            val σ = Σ(Ø, Ø, Ø)
            val pve = AssertionMalformed(a)
            var t: Term = null
            ev.eval(σ, a.exp, pve, c, tv)((_t, c1) => {
              t = _t
              Success[DefaultContext[ST, H, S], ST, H, S](c1)
            })
            t
          })
        }

      decider.prover.logComment("Axioms")
      axioms.foreach(decider.prover.assume)
    })
  }
}


class DefaultVerifierFactory[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC], S <: State[ST, H, S], TV <: TraceView[TV, ST, H, S]]
  extends VerifierFactory[DefaultVerifier[ST, H, PC, S, TV], TV, ST, H, PC, S]
{

  def create(config: Config,
      decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]],
      stateFactory: StateFactory[ST, H, S],
      typeConverter: TypeConverter,
      chunkFinder: ChunkFinder[ST, H, S, DefaultContext[ST, H, S], TV],
      stateFormatter: StateFormatter[ST, H, S, String],
      heapMerger: HeapMerger[H],
      stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
      bookkeeper: Bookkeeper,
      traceviewFactory: TraceViewFactory[TV, ST, H, S]) =

        new DefaultVerifier[ST, H, PC, S, TV](config, decider,
                       stateFactory, typeConverter, chunkFinder,
                       stateFormatter, heapMerger, stateUtils, bookkeeper, traceviewFactory)

}

class DefaultVerifier[ST <: Store[ST], H <: Heap[H], PC <: PathConditions[PC],
											S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		(	val config: Config,
			val decider: Decider[PermissionsTuple, ST, H, PC, S, DefaultContext[ST, H, S]],
			val stateFactory: StateFactory[ST, H, S],
			val typeConverter: TypeConverter,
			val chunkFinder: ChunkFinder[ST, H, S, DefaultContext[ST, H, S], TV],
			val stateFormatter: StateFormatter[ST, H, S, String],
			val heapMerger: HeapMerger[H],
      val stateUtils: StateUtils[ST, H, PC, S, DefaultContext[ST, H, S]],
			val bookkeeper: Bookkeeper,
      val traceviewFactory: TraceViewFactory[TV, ST, H, S])
		extends AbstractVerifier[ST, H, PC, S, TV]
			with Logging
{

  val contextFactory = new DefaultContextFactory[ST, H, S]

	val ev = new DefaultElementVerifier(config, decider,
																		 stateFactory, typeConverter, chunkFinder,
																		 stateFormatter, heapMerger, stateUtils, bookkeeper,
                                     contextFactory, traceviewFactory)
}
