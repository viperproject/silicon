package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import semper.sil.ast.{DomainAxiom, DomainType}
import semper.sil.ast.utility.Nodes
import sil.verifier.PartialVerificationError
import sil.verifier.errors.{ContractNotWellformed, PostconditionViolated, Internal, FunctionNotWellformed,
    PredicateNotWellformed}
import interfaces.{VerificationResult, Success, Producer, Consumer, Executor, Evaluator}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapMerger}
import state.{terms, TypeConverter, DirectChunk}
import state.terms.{Term, DefaultFractionalPermissions/*, TypeOf*/}
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
  /*protected*/ val typeConverter: TypeConverter

  /* Must be set when a program verification is started! */
  var program: ast.Program = null

  def contextFactory: ContextFactory[DefaultContext[ST, H, S], ST, H, S]
  def traceviewFactory: TraceViewFactory[TV, ST, H, S]

  def verify(member: ast.Member/*, history: History[ST, H, S]*/): VerificationResult = member match {
    case m: ast.Method => verify(m)
    case f: ast.Function => verify(f)
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

  def verify(function: ast.Function/*, h: History[ST, H, S]*/): VerificationResult = {
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

    val vThis = predicate.formalArg.localVar
    val tThis = fresh(vThis)

    val γ = Γ(vThis -> tThis)
    val σ = Σ(γ, Ø, Ø)

    inScope {
      assume(tThis !== terms.Null())
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
			val typeConverter: TypeConverter,
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
      typeConverter: TypeConverter,
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

  def decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]]
  def config: Config
  def bookkeeper: Bookkeeper

  val ev: AbstractElementVerifier[ST, H, PC, S, TV]
  import ev.typeConverter.toSort

  def verify(prog: ast.Program): List[VerificationResult] = {
    ev.program = prog

    val concreteDomainTypes = Nodes.concreteDomainTypes(prog)

    emitDomainDeclarations(concreteDomainTypes)
    emitSortWrappers(concreteDomainTypes)

    emitFunctionDeclarations(prog.functions)

    val members = prog.members.iterator

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

  /* TODO: Merge code with similar code in def emitDomainDeclarations below. */
  private def emitFunctionDeclarations(fs: Seq[ast.Function]) {
    fs.foreach(f => {
      var args: List[terms.Sort] = f.formalArgs.map(a => toSort(a.typ)).toList
      args = terms.sorts.Snap :: args /* Snapshot, and all declared parameters */
      decider.prover.declareFunction(decider.prover.sanitizeSymbol(f.name), args, toSort(f.typ))
    })
  }

  private def emitSortWrappers(concreteDomainTypes: Seq[DomainType]) {
    assert(concreteDomainTypes forall (_.isConcrete), "Expected only concrete domain types")

    val snapSortId = decider.prover.termConverter.convert(terms.sorts.Snap)

//    decider.prover.logComment("")
//    decider.prover.logComment("Declaring additional sort wrappers")
//    decider.prover.logComment("")
//
//    domains.foreach(d => {
//      val domainSort = typeConverter.toSort(ast.types.DomainType(d, Map.empty))
//      val domainSortId = decider.prover.termConverter.convert(domainSort)
//      val toSnapId = "$SortWrappers.%sTo%s".format(domainSortId, snapSortId)
//      val fromSnapId = "$SortWrappers.%sTo%s".format(snapSortId, domainSortId)
//      /* TODO: Sort wrapper naming schema must be the same as used by the
//       *       TermConverter when converting SortWrapper(t, to) terms!!!
//       */
//
//      decider.prover.declareFunction(decider.prover.sanitizeSymbol(toSnapId), Seq(domainSort), terms.sorts.Snap)
//      decider.prover.declareFunction(decider.prover.sanitizeSymbol(fromSnapId), Seq(terms.sorts.Snap), domainSort)
//    })
  }

  private def emitDomainDeclarations(concreteDomainTypes: Seq[DomainType]) {
    assert(concreteDomainTypes forall (_.isConcrete), "Expected only concrete domain types")

    decider.prover.logComment("")
    decider.prover.logComment("Declaring additional domains")
    decider.prover.logComment("")

    /* Declare domains. */
    concreteDomainTypes.foreach(dt => {
      decider.prover.logComment("Declaring domain " + dt)
      decider.prover.declareSort(toSort(dt))
    })

    /* Declare functions and predicates of each domain.
     * Since these can reference arbitrary other domains, it is crucial that all domains have
     * already been declared.
     */
    concreteDomainTypes.foreach(dt => {
      decider.prover.logComment("Functions of " + dt)

      dt.domain.functions.foreach(f =>
        decider.prover.declareFunction(
          decider.prover.sanitizeSymbol(f.name),
          f.formalArgs.map(a => toSort(a.typ.substitute(dt.typVarsMap))),
          toSort(f.typ.substitute(dt.typVarsMap))))
    })

    /* Axiomatise each domain.
     * Since the axioms can reference arbitrary domains, functions and predicates, it is crucial
     * that all these have already been declared.
     */
    concreteDomainTypes.foreach(dt => {
      decider.prover.logComment("Axiomatising domain " + dt)

      dt.domain.axioms.foreach(ax => {
        decider.prover.logComment("Axiom " + ax.name)

        val tAx = translateDomainAxiom(ax, dt.typVarsMap)
        decider.prover.assume(tAx)
      })
    })

//    decider.prover.logComment("")
//    decider.prover.logComment("Unique domain constants")
//    decider.prover.logComment("")
//
//    val uniqueFunctions = domains flatMap (_.functions) filter(_.unique)
//    assert(uniqueFunctions forall (_.formalArgs.length == 0),
//           s"Expected all unique domain functions to be nullary functions: $uniqueFunctions")
//
//    val uniqueSymbols = uniqueFunctions map (f => decider.prover.sanitizeSymbol(f.name))
//
//    if (uniqueSymbols.nonEmpty) decider.prover.assume(terms.Distinct(uniqueSymbols))
  }

  private def translateDomainAxiom(ax: DomainAxiom, typeVarMap: Map[ast.TypeVar, ast.Type]): Term = {
    translateExp((t: ast.Type) => toSort(t.substitute(typeVarMap)))(ax.exp)
  }

  private def translateExp(toSort: ast.Type => terms.Sort)(exp: ast.Expression): Term = {
    val f = translateExp(toSort) _

    exp match {
      case q @ ast.Quantified(qvars, body) =>
        val quantifier = q match {
          case _: ast.Forall => terms.Forall
          case _: ast.Exists => terms.Exists
        }
        terms.Quantification(quantifier, qvars map (v => terms.Var(v.name, toSort(v.typ))), f(body))

      case ast.True() => terms.True()
      case ast.False() => terms.False()
      case ast.Not(e0) => terms.Not(f(e0))
      case ast.And(e0, e1) => terms.And(f(e0), f(e1))
      case ast.Or(e0, e1) => terms.Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => terms.Implies(f(e0), f(e1))
      case ast.Ite(e0, e1, e2) => terms.Ite(f(e0), f(e1), f(e2))

      case ast.Equals(e0, e1) => terms.TermEq(f(e0), f(e1))
      case ast.Unequals(e0, e1) => terms.Not(terms.TermEq(f(e0), f(e1)))

      case ast.IntegerLiteral(n) => terms.IntLiteral(n)
      case ast.IntPlus(e0, e1) => terms.Plus(f(e0), f(e1))
      case ast.IntMinus(e0, e1) => terms.Minus(f(e0), f(e1))
      case ast.IntTimes(e0, e1) => terms.Times(f(e0), f(e1))
      case ast.IntDiv(e0, e1) => terms.Div(f(e0), f(e1))
      case ast.IntMod(e0, e1) => terms.Mod(f(e0), f(e1))
      case ast.IntNeg(e0) => terms.Minus(0, f(e0))

      case ast.IntGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.IntGT(e0, e1) => terms.Greater(f(e0), f(e1))
      case ast.IntLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.IntLT(e0, e1) => terms.Less(f(e0), f(e1))

      case ast.NullLiteral() => terms.Null()

      case v: ast.Variable => terms.Var(v.name, toSort(v.typ))

      case ast.DomainFuncApp(func, args, typeVarMap) =>
        /* TODO: Is it safe to ignore the typeVarMap when translating the args? */
        terms.DomainFApp(func.name, args map f, toSort(exp.typ))

      case _: sil.ast.SeqExp => ???

      case   _: ast.PermissionExpression | _: ast.FieldRead | _: ast.AccessPredicate | _: ast.Old
           | _: ast.FractionalPerm | _: ast.PermGE | _: ast.PermGT | _: ast.PermLE | _: ast.PermLT | _: ast.IntPermTimes
           | _: ast.PermPlus | _: ast.PermMinus | _: ast.PermTimes | _: ast.ResultLiteral | _: ast.Unfolding
           | _: ast.InhaleExhaleExp | _: ast.PredicateLocation | _: ast.FuncApp =>
        sys.error(s"Found unexpected expresion $exp")
    }
  }
}


class DefaultVerifierFactory[ST <: Store[ST],
                             H <: Heap[H],
                             PC <: PathConditions[PC],
                             S <: State[ST, H, S],
                             TV <: TraceView[TV, ST, H, S]]
  extends VerifierFactory[DefaultVerifier[ST, H, PC, S, TV], TV, ST, H, PC, S]
{

  def create(config: Config,
      decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
      stateFactory: StateFactory[ST, H, S],
      typeConverter: TypeConverter,
      chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
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
			val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, DefaultContext[ST, H, S]],
			val stateFactory: StateFactory[ST, H, S],
			val typeConverter: TypeConverter,
			val chunkFinder: ChunkFinder[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV],
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
