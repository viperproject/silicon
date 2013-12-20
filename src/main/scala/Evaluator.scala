package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.errors.PreconditionInAppFalse
import sil.verifier.reasons.{DivisionByZero, ReceiverNull, NonPositivePermission}
import reporting.{LocalIfBranching, Bookkeeper, Evaluating, DefaultContext, LocalAndBranching,
    ImplBranching, IfBranching, LocalImplBranching, LocalOrBranching}
import interfaces.{Evaluator, Consumer, Producer, VerificationResult, Failure, Success}
import interfaces.state.{ChunkIdentifier, Store, Heap, PathConditions, State, StateFormatter, StateFactory,
    FieldChunk}
import interfaces.decider.Decider
import interfaces.reporting.{TraceView}
import semper.silicon.state._
import state.terms._
import state.terms.implicits._
import semper.silicon.heap.HeapManager
import semper.silicon.interfaces.Failure
import scala.Some
import semper.silicon.state.terms.False
import semper.silicon.state.terms.Eq
import semper.silicon.state.terms.SeqSingleton
import semper.silicon.state.terms.Div
import semper.silicon.state.terms.SeqNil
import semper.silicon.state.terms.WildcardPerm
import semper.silicon.state.terms.SeqRanged
import semper.silicon.state.FieldChunkIdentifier
import semper.silicon.state.terms.Quantification
import semper.silicon.state.terms.Mod
import semper.sil.verifier.reasons.NonPositivePermission
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.terms.*
import semper.silicon.state.PredicateChunkIdentifier
import semper.silicon.state.terms.FullPerm
import semper.silicon.state.terms.SingletonSet
import semper.silicon.state.terms.TermPerm
import semper.silicon.reporting.DefaultContext
import semper.silicon.interfaces.Success
import semper.silicon.state.terms.True
import semper.silicon.state.terms.IntLiteral
import semper.silicon.state.terms.Null
import semper.silicon.state.terms.FApp
import semper.silicon.state.terms.EmptySet
import semper.silicon.state.terms.NoPerm
import semper.sil.verifier.errors.PreconditionInAppFalse
import semper.silicon.state.terms.FractionPerm
import semper.sil.verifier.reasons.ReceiverNull
import semper.sil.verifier.reasons.DivisionByZero

trait DefaultEvaluator[
                       ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
											 S <: State[ST, H, S],
											 TV <: TraceView[TV, ST, H, S]]
		extends Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV] with HasLocalState
		{ this: Logging with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
										with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
										with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val symbolConverter: SymbolConvert
	import symbolConverter.toSort

	protected val chunkFinder: ChunkFinder[P, ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val stateUtils: StateUtils[ST, H, PC, S, C]

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config
	protected val bookkeeper: Bookkeeper

  protected val heapManager: HeapManager[ST, H, PC, S, C, TV]


	private var fappCache: Map[Term, Set[Term]] = Map()
	private var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C, tv: TV)
			     (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

		evals2(σ, es, Nil, pve, c, tv)((ts, c1) =>
			Q(ts, c1))

	def evalp(σ: S, p: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			     (Q: (P, C) => VerificationResult)
           : VerificationResult = {

    eval(σ, p, pve, c, tv)((tp, c1) => tp match {
      case fp: DefaultFractionalPermissions => Q(fp, c1)
      case _ => Q(TermPerm(tp), c1)})
  }

	private def evals2(σ: S,
                     es: Seq[ast.Expression],
                     ts: List[Term],
                     pve: PartialVerificationError,
                     c: C,
                     tv: TV)
                    (Q: (List[Term], C) => VerificationResult)
                    : VerificationResult = {

		if (es.isEmpty)
			Q(ts.reverse, c)
		else
			eval(σ, es.head, pve, c, tv)((t, c1) =>
				evals2(σ, es.tail, t :: ts, pve, c1, tv)(Q))
	}

	def eval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {

		eval2(σ, e, pve, c, tv)((t, c1) =>
			Q(t, c1))
  }

  protected def eval2(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

    val tv1 = tv.stepInto(c, Evaluating[ST, H, S](σ, e))

    internalEval(σ, e, pve, c, tv1)((t, c1) => {
      tv1.currentStep.σPost = σ
      Q(t, c1)
    })
  }

	/* Attention: Only use eval(σ, e, m, c, tv)(Q) inside of internalEval, because
	 *   - eval adds an "Evaluating" operation to the context
	 *   - eval sets the source node of the resulting term
	 */
	private def internalEval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
                          (Q: (Term, C) => VerificationResult)
                          : VerificationResult = {

		/* For debugging only */
		e match {
			case  _: ast.True | _: ast.False | _: ast.NullLiteral | _: ast.IntegerLiteral | _: ast.FullPerm | _: ast.NoPerm
          | _: ast.Variable | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.ResultLiteral
          | _: ast.WildcardPerm | _: ast.FieldAccess =>

			case _ =>
				logger.debug("\nEVALUATING " + e)
				logger.debug(stateFormatter.format(σ))
        decider.prover.logComment(s"[eval] $e")
		}

    //println(e)
    //println(e.getClass)

    /* Since commit 0cf1f26, evaluating unfoldings is a local operation, and it
     * might be tempting to think that we don't need to locally evaluate
     * Implies and Ite anymore. However, that is not true, because not all of
     * them occur in the context of an unfolding. They can also occur in a
     * pre/postcondition such as 'requires b1 ==> b2', in which case Silicon
     * still shouldn't branch.
     */

    val resultTerm = e match {
      case ast.True() => Q(True(), c)
      case ast.False() => Q(False(), c)

      case ast.NullLiteral() => Q(Null(), c)
      case ast.IntegerLiteral(bigval) => Q(IntLiteral(bigval), c)

      case ast.Equals(e0, e1) => evalBinOp(σ, e0, e1, Eq, pve, c, tv)(Q)
      case ast.Unequals(e0, e1) => evalBinOp(σ, e0, e1, (p0: Term, p1: Term) => Not(Eq(p0, p1)), pve, c, tv)(Q)

      case v: ast.Variable => {
        Q(σ.γ(v), c)
      }

      case _: ast.FullPerm => Q(FullPerm(), c)
      case _: ast.NoPerm => Q(NoPerm(), c)

      case ast.FractionalPerm(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => FractionPerm(t0, t1), pve, c, tv)((tFP, c1) =>
          failIfDivByZero(tFP, e1, tFP.d, TermPerm(0), pve, c1, tv)(Q))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = stateUtils.freshARP()
        assume(tConstraints)
        Q(WildcardPerm(tVar), c)

      case _: ast.EpsilonPerm =>
        sys.error(s"Found unexpected expression $e (${e.getClass.getName}})")
//        Q(EpsilonPerm(), c)

      case ast.CurrentPerm(locacc) =>
        withChunkIdentifier(σ, locacc, true, pve, c, tv)((id, c1) =>
          decider.getChunk[DirectChunk](σ.h, id) match {
            case Some(ch) => Q(ch.perm, c1)
            case None => Q(NoPerm(), c1)
          })

      case fa: ast.FieldAccess =>  {
        // TODO: should not be needed - migrate all value lookups into heapmanager
        val hasCondChunks = σ.h.values exists {case ch:DirectConditionalChunk => true case _ => false}

        if (hasCondChunks) {
          eval(σ, fa.rcv, pve, c, tv)((tRcvr, c1) =>
            heapManager.getValue(σ.h, tRcvr, fa.field, null, pve, fa, c, tv) ((t) => Q(t, c1))
          )
        } else {
          withChunkIdentifier(σ, fa, true, pve, c, tv)((id, c1) =>
            withChunk[FieldChunk](σ.h, id, fa, pve, c1, tv)(ch =>
              Q(ch.value, c1)))
        }
      }

      case ast.Not(e0) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          Q(Not(t0), c1))

      case ast.IntNeg(e0) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          Q(Minus(0, t0), c1))

      case ast.Old(e0) => eval(σ \ σ.g, e0, pve, c, tv)(Q)

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, And, pve, c, tv)(Q)

      /* Short-circuiting evaluation of AND */
      case ast.And(e0, e1) =>
        /* TODO: It should no longer be possible to accumulate local results, because
         *       all branching constructs are locally evaluated themselves.
         *       Hence, implement evaluation of AND similar to that of OR.
         *       Try to reuse code!
         */
        //println("Evaluating And")
        decider.prover.logComment("Evaluating And")
        var πPre: Set[Term] = Set()
        var t0: Option[Term] = None
        var localResults: List[LocalEvaluationResult] = Nil

        eval(σ, e0, pve, c, tv)((_t0, c1) => {
          assert(t0.isEmpty || t0.get == _t0, s"Unexpected difference: $t0 vs ${_t0}")

          t0 = Some(_t0)
          πPre = decider.π

          decider.pushScope()
          /* TODO: Add a branch-function that only takes a true-continuation.
          *       Give it a more appropriate name, one that expresses
          *       that it is more a continue-if-no-contradiction thing.
          */
          val r =
            branchLocally(t0.get, c1, tv, LocalAndBranching(e0, t0.get),
              (c2: C, tv1: TV) =>
                eval(σ, e1, pve, c2, tv1)((_t1, c3) => {
                  localResults ::= LocalEvaluationResult(guards, _t1, decider.π -- (πPre + t0.get))
                  Success[C, ST, H, S](c3)}),
              (c2: C, tv1: TV) => Success[C, ST, H, S](c2))

          decider.popScope()

          r && {
            val (t1: Term, tAux: Set[Term]) = combine(localResults)
            assume(tAux)
            //println("End Evaluating And")
            decider.prover.logComment("End Evaluating And")

            Q(And(t0.get, t1), c1)}})

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, Or, pve, c, tv)(Q)

      /* Short-circuiting evaluation of OR */
      case ast.Or(e0, e1) =>
        /* Evaluating the disjuncts should never non-locally branch, because
         *   1. OR may not contain any access predicates, and consequently no impure conditionals
         *   2. OR may contain an unfolding, but it will be evaluated locally, thus any
         *      potential branching should not be witnessed by the evaluation of OR.
         * It should therefore not be necessary to accumulate local evaluation results, or to
         * consider the brancher guards.
         */
        var πPre: Set[Term] = Set()
        var t0: Option[Term] = None
        var t1: Option[Term] = None
        var πt1: Set[Term] = Set()

        eval(σ, e0, pve, c, tv)((_t0, c1) => {
          assert(t0.isEmpty, s"Unexpected branching occurred while locally evaluating $e0")
          t0 = Some(_t0)
          πPre = decider.π

          decider.pushScope()
          /* TODO: See comment to short-circuiting evaluation of AND */
          val t0Neg = Not(t0.get)
          val r =
            branchLocally(t0Neg, c1, tv, LocalOrBranching(e0, t0Neg),
              (c2: C, tv1: TV) =>
                eval(σ, e1, pve, c2, tv1)((_t1, c3) => {
                  assert(t1.isEmpty, s"Unexpected branching occurred while locally evaluating $e1")
                  t1 = Some(_t1)
                  πt1 = decider.π -- (πPre + t0Neg) /* Removing t0Neg from πt1 is crucial! */
                  Success[C, ST, H, S](c3)}),
              (c2: C, tv1: TV) => Success[C, ST, H, S](c2))
          decider.popScope()

          r && {
            val tAux = state.terms.utils.BigAnd(πt1)
            val tOr = Or(t0.get, t1.getOrElse(True()))
            assume(tAux)
            Q(tOr, c1)}})

      case _: ast.Implies if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c, tv)(Q)

      case impl @ ast.Implies(e0, e1) =>
        /* - Problem with Implies(e0, e1) is that simply evaluating e1 after e0
         *   fails if e0 establishes a precondition of e1
         * - Hence we have to assume e0 when evaluating e1, but revoke that
         *   assumption afterwards
         * - We also have to keep track of all path conditions that result from
         *   the evaluation of e0 and e1
         */

        val πPre: Set[Term] = decider.π
          /* Initial set of path conditions */

        var πIf: Set[Term] = Set()
          /* Path conditions assumed while evaluating the antecedent */
        var tEvaluatedIf: Term = False()
          /* The term the antecedent actually evaluates too. */

        var localResults: List[LocalEvaluationResult] = Nil

        decider.pushScope()
        val r =
          eval(σ, e0, pve, c, tv)((t0, c1) => {
            val πDiff = decider.π -- πPre

            assert(tEvaluatedIf == False() || tEvaluatedIf == t0, s"Unexpected difference: $tEvaluatedIf vs $t0")
            assert(πIf.isEmpty || πIf == πDiff, s"Unexpected difference: $πIf vs $πDiff")

            πIf = πDiff
            tEvaluatedIf = t0

            branchLocally(t0, c1, tv, LocalImplBranching[ST, H, S](e0, t0),
              (c2: C, tv1: TV) =>
                eval(σ, e1, pve, c2, tv1)((t1, c3) => {
                  localResults ::= LocalEvaluationResult(guards, t1, decider.π -- (πPre ++ πIf + tEvaluatedIf))
                  Success[C, ST, H, S](c3)}),
              (c2: C, _) => Success[C, ST, H, S](c2))})

        decider.popScope()

        r && {
          /* The additional path conditions gained while evaluating the
           * antecedent can be assumed in any case.
           * If the antecedent holds, then the additional path conditions
           * related to the consequent can also be assumed.
           */

          val (tActualThen: Term, tAuxThen: Set[Term]) = combine(localResults)
          val tAuxIf = state.terms.utils.BigAnd(πIf)

          val tImplies = Implies(tEvaluatedIf, tActualThen)
          val tAuxImplies = Implies(tEvaluatedIf, state.terms.utils.BigAnd(tAuxThen))

          assume(Set(tAuxIf, tAuxImplies))
          Q(tImplies, c)
        }

      case _: ast.Ite if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c, tv)(Q)

      case ite @ ast.Ite(e0, e1, e2) =>
        val πPre: Set[Term] = decider.π
        var πIf: Option[Set[Term]] = None
        var tActualIf: Option[Term] = None

        var localResultsThen: List[LocalEvaluationResult] = Nil
        var localResultsElse: List[LocalEvaluationResult] = Nil

        decider.pushScope()

        val r =
          eval(σ, e0, pve, c, tv)((t0, c1) => {
            val πDiff = decider.π -- πPre

            assert(tActualIf.isEmpty || tActualIf.get == t0, s"Unexpected difference: $tActualIf vs $t0")
            assert(πIf.isEmpty || πIf.get == πDiff, s"Unexpected difference: $πIf vs $πDiff")

            πIf = Some(πDiff)
            tActualIf = Some(t0)

            branchLocally(t0, c1, tv, LocalIfBranching[ST, H, S](e0, t0),
              (c2: C, tv1: TV) => {
                eval(σ, e1, pve, c2, tv1)((t1, c3) => {
                  localResultsThen ::= LocalEvaluationResult(guards, t1, decider.π -- (πPre ++ πIf.get + t0))
                  Success[C, ST, H, S](c3)})},

              (c2: C, tv1: TV) => {
                eval(σ, e2, pve, c2, tv1)((t2, c3) => {
                  localResultsElse ::= LocalEvaluationResult(guards, t2, decider.π -- (πPre ++ πIf.get + Not(t0)))
                  Success[C, ST, H, S](c3)})})})

        decider.popScope()

        r && {
          /* Conjunct all auxiliary terms (sort: bool). */
          val tAuxIf: Term = state.terms.utils.BigAnd(πIf.getOrElse(Set(False())))

          val tActualThenVar = fresh("actualThen", toSort(e1.typ))
          val tActualElseVar = fresh("actualElse", toSort(e2.typ))

          /* TODO: Does it increase prover performance if the actualXXXVar terms include tActualIf in the
           *       antecedent of the implication? I.e. 'guard && tActualIf ==> actualResult'? */
          val (tActualThen: Term, tAuxThen: Set[Term]) = combine(localResultsThen, tActualThenVar === _)
          val (tActualElse: Term, tAuxElse: Set[Term]) = combine(localResultsElse, tActualElseVar === _)

          /* Ite with auxiliary terms */
          val tAuxIte = Ite(tActualIf.getOrElse(False()),
                            state.terms.utils.BigAnd(tAuxThen),
                            state.terms.utils.BigAnd(tAuxElse))

          /* Ite with the actual results of the evaluation */
          val tActualIte =
            Ite(tActualIf.getOrElse(False()),
                if (localResultsThen.nonEmpty) tActualThenVar else fresh("$deadThen", toSort(e1.typ)),
                if (localResultsElse.nonEmpty) tActualElseVar else fresh("$deadElse", toSort(e2.typ)))

          val actualTerms = And(tActualThen, tActualElse)

          assume(Set(tAuxIf, tAuxIte, actualTerms))
          Q(tActualIte, c)
        }

      /* Integers */

      case ast.IntPlus(e0, e1) =>
        evalBinOp(σ, e0, e1, Plus, pve, c, tv)(Q)

      case ast.IntMinus(e0, e1) =>
        evalBinOp(σ, e0, e1, Minus, pve, c, tv)(Q)

      case ast.IntTimes(e0, e1) =>
        evalBinOp(σ, e0, e1, Times, pve, c, tv)(Q)

      case ast.IntDiv(e0, e1) =>
        evalBinOp(σ, e0, e1, Div, pve, c, tv)((tDiv, c1) =>
          failIfDivByZero(tDiv, e1, tDiv.p1, 0, pve, c1, tv)(Q))

      case ast.IntMod(e0, e1) =>
        evalBinOp(σ, e0, e1, Mod, pve, c, tv)((tMod, c1) =>
          failIfDivByZero(tMod, e1, tMod.p1, 0, pve, c1, tv)(Q))

      case ast.IntLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c, tv)(Q)

      case ast.IntLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c, tv)(Q)

      case ast.IntGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c, tv)(Q)

      case ast.IntGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c, tv)(Q)

      /* Permissions */

      case ast.PermPlus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 + t1, pve, c, tv)(Q)

      case ast.PermMinus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 - t1, pve, c, tv)(Q)

      case ast.PermTimes(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 * t1, pve, c, tv)(Q)

      case ast.IntPermTimes(e0, e1) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          evalp(σ, e1, pve, c1, tv)((t1, c2) =>
            Q(IntPermTimes(t0, t1), c2)))

      case ast.PermLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c, tv)(Q)

      case ast.PermLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c, tv)(Q)

      case ast.PermGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c, tv)(Q)

      case ast.PermGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c, tv)(Q)

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(func, eArgs, _) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = toSort(dfa.typ)
          val fi = symbolConverter.toFunction(func, inSorts :+ outSort)
          Q(DomainFApp(fi, tArgs), c1)})

      /* TODO: Implement a non-local evaluation of quantifiers. */

      case quant: ast.Quantified =>
        val body = quant.exp
        val vars = quant.variables map (_.localVar)

        val tQuantOp = quant match {
          case _: ast.Forall => Forall
          case _: ast.Exists => Exists
        }

        /* Why so cumbersome? Why not simply eval(..., tBody => Q(..., tBody))?
         *  - Assume we have a quantification forall x: int :: x > 0 ==> f(x) > 0
         *  - Evaluating the body yields a term Implies(lhs, rhs) which will be
         *    used as the body if the Quantification term
         *  - The evaluation also yields additional path conditions, for example
         *    the relation between the function application and the evaluated
         *    function body, e.g. f(x) == 2x
         *  - These are not returned but added to the path conditions during they
         *    evaluation of the function application
         *  - However, we need them to occur inside the quantification, not
         *    outside of it, because assumptions outside of the quantification
         *    will not be considered even if the quantified variable occurs in
         *    them due to the scope of the quantified variables
         *  - We thus have to determine these additional path conditions
         *    to be able to include them in the quantification
         *
         * ATTENTION The current implementation unfortunately disallows branching
         * evaluations!
         * Consider e.g. e0 ==> e1 which could be evaluated by
         * branching over e0, returning once t0 ==> t1 and once ¬t0 ==> true.
         * However, the second branch's result overwrites the first branch's
         * result when being assigned to tActualBody. Hence, only the second
         * branch is asserted which always succeeds.
         *
         * A possible solution would be to make tActualBody and πPost lists and
         * to eventually invoke Q with a list of conjuncted quantifications.
         */

        val πPre: Set[Term] = decider.π
        var localResults: List[LocalEvaluationResult] = Nil

        decider.pushScope()

        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ(vars zip tVars)

        val r =
          eval(σ \+ γVars, body, pve, c, tv)((tBody, c1) => {
            localResults ::= LocalEvaluationResult(guards, tBody, decider.π -- πPre)

            /* We could call Q directly instead of returning Success, but in
             * that case the path conditions πDelta would also be outside of
             * the quantification. Since they are not needed outside of the
             * quantification we go the extra mile to get ride of them in order
             * to not pollute the path conditions.
             *
             * Actually, only path conditions in which the quantified variable
             * occurs are waste, others, especially $combine-terms, are actually
             * of interest and should be in the path conditions to avoid the
             * 'fapp-requires-separating-conjunction-fresh-snapshots' problem,
             * which is currently overcome by caching fapp-terms.
             */
            Success[C, ST, H, S](c1)})

        decider.prover.logComment(s"END EVAL QUANT $quant")
        decider.popScope()

        r && {
          val (tActual: Term, tAux: Set[Term]) = combine(localResults)
          val tQuantAux = Quantification(tQuantOp, tVars, state.terms.utils.BigAnd(tAux))
          val tQuant = Quantification(tQuantOp, tVars, tActual)
          assume(tQuantAux)
          Q(tQuant, c)}

      case fapp @ ast.FuncApp(func, eArgs) =>
        decider.prover.logComment("evaluating " + func.name)
        val err = PreconditionInAppFalse(fapp)

        evals2(σ, eArgs, Nil, pve, c, tv)((tArgs, c2) => {
          bookkeeper.functionApplications += 1
          val insγ = Γ(func.formalArgs.map(_.localVar).zip(tArgs))
          val σ2 = σ \ insγ
          val pre = ast.utils.BigAnd(func.pres)
          consume(σ2, FullPerm(), pre, err, c2, tv)((_, s, _, c3) => {
            decider.prover.logComment("consumed the preconditions")
            val tFA = FApp(symbolConverter.toFunction(func), s.convert(sorts.Snap), tArgs)
            if (fappCache.contains(tFA)) {
              logger.debug("[Eval(FApp)] Took cache entry for " + fapp)
              val piFB = fappCache(tFA)
              assume(piFB)
              Q(tFA, c3)
            } else {
              val σ3 = σ2 \+ (func.result, tFA)
              /* Break recursive cycles */
              if (c3.cycles(func) < config.unrollFunctions()) {
                val c3a = c3.incCycleCounter(func)
                val πPre = decider.π
                val post = ast.utils.BigAnd(func.posts)
                bookkeeper.functionBodyEvaluations += 1
                eval(σ3, func.exp, pve, c3a, tv)((tFB, c4) =>
                  eval(σ3, post, pve, c4, tv)((tPost, c5) => {
                    val c5a = c5.decCycleCounter(func)
                    val tFAEqFB = Implies(state.terms.utils.BigAnd(guards), tFA === tFB)
                    if (!config.disableFunctionApplicationCaching())
                      fappCache += (tFA -> (decider.π -- πPre + tFAEqFB + tPost))
                    assume(Set(tFAEqFB, tPost))
                    Q(tFA, c5a)
                  }))

              } else {
                /* Unfolded the function often enough already. We still need to
                 * evaluate the postcondition, though, because Z3 might
                 * otherwise not know enough about the recursive call.
                 * For example, that the length of a list is always positive.
                 */
                val post = ast.utils.BigAnd(func.posts)

                /* TODO: Probably doesn't detect mutual recursion. */
                val badPostcondition =
                  post existsDefined {
                    case ast.FuncApp(someFunc, _) if func.name == someFunc.name =>
                  }

                if (badPostcondition)
                  sys.error(  "Silicon cannot handle function postconditions that mention the function itself. "
                            + "Try to replace the function application by 'result', if possible.")

                val πPre = decider.π
                eval(σ3, post, pve, c3, tv)((tPost, c4) => {
                  if (!config.disableFunctionApplicationCaching())
                    fappCache += (tFA -> (decider.π -- πPre + tPost))
                  assume(tPost)
                  Q(tFA, c4)})}}})})

      case _: ast.Unfolding if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c, tv)(Q)

      case ast.Unfolding(
                acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm),
                eIn) =>
        //println("Unfolding " + acc.loc.predicate.name)
        /* Unfolding only has a temporary effect on the current heap because
         * the resulting heap is not forwarded to the final continuation.
         */
        var πPre: Set[Term] = Set()
        var tPerm: Option[Term] = None
        var localResults: List[LocalEvaluationResult] = Nil
        decider.prover.logComment("unfolding " + acc.loc.predicate.name)

        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0a = c.incCycleCounter(predicate)

          val r =
            evalp(σ, ePerm, pve, c0a, tv)((_tPerm, c1) => {
              assert(tPerm.isEmpty || tPerm.get == _tPerm, s"Unexpected difference: $tPerm vs ${_tPerm}")
              tPerm = Some(_tPerm)
              πPre = decider.π
              if (decider.isPositive(_tPerm))
                evals(σ, eArgs, pve, c1, tv)((tArgs, c2) =>
                  consume(σ, FullPerm(), acc, pve, c2, tv)((σ1, snap, _, c3) => {
                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                    decider.prover.logComment("producing predicate body!")
                    produce(σ1 \ insγ, s => snap.convert(s), _tPerm, predicate.body, pve, c3, tv)((σ2, c4) => {
                      val c4a = c4.decCycleCounter(predicate)
                      val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
                      eval(σ3, eIn, pve, c4a, tv)((tIn, c5) => {
                        localResults ::= LocalEvaluationResult(guards, tIn, decider.π -- πPre)
                        Success[C, ST, H, S](c3)})})}))
              else
                Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c1, tv)})

          r && {
            val tActualInVar = fresh("actualIn", toSort(eIn.typ))
            val (tActualIn: Term, tAuxIn: Set[Term]) = combine(localResults, tActualInVar === _)
              /* TODO: See comment about performance in case ast.Ite */
            decider.prover.logComment("assuming in unfolding... " + acc.loc.predicate.name)
            assume(tAuxIn + tActualIn)
            //println("Done unfolding " + acc.loc.predicate.name)
            Q(tActualInVar, c)
          }
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> unfolding next.P in e} is currently not " +
            "supported in Syxc. It should be  possible to wrap 'unfolding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + e)

      /* Sequences */

      case sil.ast.SeqContains(e0, e1) => evalBinOp(σ, e1, e0, SeqIn, pve, c, tv)(Q)
        /* Note the reversed order of the arguments! */

      case sil.ast.SeqAppend(e0, e1) => evalBinOp(σ, e0, e1, SeqAppend, pve, c, tv)(Q)
      case sil.ast.SeqDrop(e0, e1) => evalBinOp(σ, e0, e1, SeqDrop, pve, c, tv)(Q)
      case sil.ast.SeqTake(e0, e1) => evalBinOp(σ, e0, e1, SeqTake, pve, c, tv)(Q)
      case sil.ast.SeqIndex(e0, e1) => evalBinOp(σ, e0, e1, SeqAt, pve, c, tv)(Q)
      case sil.ast.SeqLength(e) => eval(σ, e, pve, c, tv)((t0, c1) => Q(SeqLength(t0), c1))
      case sil.ast.EmptySeq(typ) => Q(SeqNil(toSort(typ)), c)
      case sil.ast.RangeSeq(e0, e1) => evalBinOp(σ, e0, e1, SeqRanged, pve, c, tv)(Q)

      case sil.ast.SeqUpdate(e0, e1, e2) =>
        evals2(σ, List(e0, e1, e2), Nil, pve, c, tv)((ts, c1) =>
          Q(SeqUpdate(ts(0), ts(1), ts(2)), c1))

      case sil.ast.ExplicitSeq(es) =>
        evals2(σ, es.reverse, Nil, pve, c, tv)((tEs, c1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(SeqSingleton(te), tSeq))
          assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(tSeq, c1)})

      /* Sets and multisets */

      case sil.ast.EmptySet(typ) => Q(EmptySet(toSort(typ)), c)

      case sil.ast.ExplicitSet(es) =>
        evals2(σ, es, Nil, pve, c, tv)((tEs, c1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(tSet, c1)})

      case sil.ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetUnion, pve, c, tv)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetUnion, pve, c, tv)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case sil.ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIntersection, pve, c, tv)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIntersection, pve, c, tv)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case sil.ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetSubset, pve, c, tv)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetSubset, pve, c, tv)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case sil.ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetDifference, pve, c, tv)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, SetDifference, pve, c, tv)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case sil.ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIn, pve, c, tv)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIn, pve, c, tv)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case sil.ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.types.Set => eval(σ, e0, pve, c, tv)((t0, c1) => Q(SetCardinality(t0), c1))
        case _: ast.types.Multiset => eval(σ, e0, pve, c, tv)((t0, c1) => Q(MultisetCardinality(t0), c1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }
		}

    resultTerm
	}

  /* The non-local evaluations are only intended for benchmarking and
   * debugging reasons, because they can result in incompletenesses.
   */
  private def nonLocalEval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
                          (Q: (Term, C) => VerificationResult)
                          : VerificationResult = {

    assert(config.disableLocalEvaluations(),
      "Unexpected call to performNonLocalEvaluation since config.localEvaluations is true.")

    e match {
      case ast.Implies(e0, e1) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => eval(σ, e1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => Q(True(), c2)))

      case ast.Ite(e0, e1, e2) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c1, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => eval(σ, e1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => eval(σ, e2, pve, c2, tv1)(Q)))

      case ast.Unfolding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm), eIn) =>
        val body = predicate.body

        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0a = c.incCycleCounter(predicate)
          evalp(σ, ePerm, pve, c0a, tv)((tPerm, c1) =>
            if (decider.isPositive(tPerm))
              evals(σ, eArgs, pve, c1, tv)((tArgs, c2) =>
                consume(σ, FullPerm(), acc, pve, c2, tv)((σ1, snap, _, c3) => {
                  val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                  /* Unfolding only effects the current heap */
                  produce(σ1 \ insγ, s => snap.convert(s), tPerm, body, pve, c3, tv)((σ2, c4) => {
                    val c4a = c4.decCycleCounter(predicate)
                    val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
                    eval(σ3, eIn, pve, c4a, tv)(Q)})}))
            else
              Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c1, tv))}
        else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> unfolding next.P in e} is currently not " +
            "supported in Syxc. It should be  possible to wrap 'unfolding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + e)

      case _ => sys.error(s"Cannot non-locally evaluate $e (${e.getClass.getName})")
    }
  }

  def withChunkIdentifier(σ: S,
                          locacc: ast.LocationAccess,
                          assertRcvrNonNull: Boolean,
                          pve: PartialVerificationError,
                          c: C,
                          tv: TV)
                         (Q: (ChunkIdentifier, C) => VerificationResult)
                         : VerificationResult =

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          if (assertRcvrNonNull)
            //if(decider.hasEnoughPermissionsGlobally(σ.h, FieldChunkIdentifier(tRcvr, field.name)))
            if (decider.assert(tRcvr !== Null()))
              Q(FieldChunkIdentifier(tRcvr, field.name), c1)
            else
              Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(locacc), c1, tv)
          else
            Q(FieldChunkIdentifier(tRcvr, field.name), c1))

      case ast.PredicateAccess(eArgs, predicate) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) =>
          Q(PredicateChunkIdentifier(predicate.name, tArgs), c1))
    }

	private def evalBinOp[T <: Term]
                       (σ: S,
			                  e0: ast.Expression,
                        e1: ast.Expression,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
			                  c: C,
                        tv: TV)
                       (Q: (T, C) => VerificationResult)
                       : VerificationResult = {

		eval(σ, e0, pve, c, tv)((t0, c1) =>
			eval(σ, e1, pve, c1, tv)((t1, c2) =>
				Q(termOp(t0, t1), c2)))
  }

  private def failIfDivByZero(t: Term,
                              eDivisor: ast.Expression,
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              c: C,
                              tv: TV)
                             (Q: (Term, C) => VerificationResult)
                             : VerificationResult = {

    if (decider.assert(tDivisor !== tZero))
      Q(t, c)
    else
      Failure[C, ST, H, S, TV](pve dueTo DivisionByZero(eDivisor), c, tv)
  }

  private def evalPermOp[PO <: P]
                        (σ: S,
                         e0: ast.Expression,
                         e1: ast.Expression,
                         permOp: (P, P) => PO,
                         pve: PartialVerificationError,
                         c: C,
                         tv: TV)
                        (Q: (PO, C) => VerificationResult)
                        : VerificationResult = {

    evalp(σ, e0, pve, c, tv)((t0, c1) =>
      evalp(σ, e1, pve, c1, tv)((t1, c2) =>
        Q(permOp(t0, t1), c2)))
  }

  private case class LocalEvaluationResult(πGuards: Seq[Term], actualResult: Term, auxiliaryTerms: Set[Term])

  private def combine(localResults: Seq[LocalEvaluationResult],
                      actualResultTransformer: Term => Term = Predef.identity)
                     : (Term, Set[Term]) = {

    val (t1: Term, tAux: Set[Term]) =
      localResults.map {lr =>
        val guard: Term = state.terms.utils.BigAnd(lr.πGuards)
        val tAct: Term = Implies(guard, actualResultTransformer(lr.actualResult))
        val tAux: Term = Implies(guard, state.terms.utils.BigAnd(lr.auxiliaryTerms))

        (tAct, tAux)
      }.foldLeft((True(): Term, Set[Term]())){case ((tActAcc, tAuxAcc), (tAct, tAux)) =>
        (And(tActAcc, tAct), tAuxAcc + tAux)
      }

    (t1, tAux)
  }

	override def pushLocalState() {
		fappCacheFrames = fappCacheFrames.push(fappCache)
		super.pushLocalState()
	}

	override def popLocalState() {
		fappCache = fappCacheFrames.top
		fappCacheFrames = fappCacheFrames.pop
		super.popLocalState()
	}
}
