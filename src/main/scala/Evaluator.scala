package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.errors.FunctionApplicationFailed
import sil.verifier.reasons.{ReceiverNull, NegativeFraction}
import reporting.{LocalIfBranching, Bookkeeper, Evaluating, DefaultContext, LocalAndBranching,
    ImplBranching, IfBranching, LocalImplBranching}
import interfaces.{Evaluator, Consumer, Producer, VerificationResult, Failure, Success}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, StateFactory,
    FieldChunk}
import interfaces.decider.Decider
import interfaces.reporting.{TraceView}
import state.{TypeConverter, DirectChunk}
import state.terms._
import state.terms.implicits._

trait DefaultEvaluator[
                       ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
											 S <: State[ST, H, S],
											 TV <: TraceView[TV, ST, H, S]]
		extends Evaluator[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV] with HasLocalState
		{ this: Logging with Consumer[PermissionsTuple, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
										with Producer[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
										with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]

	protected val decider: Decider[PermissionsTuple, ST, H, PC, S, C]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val typeConverter: TypeConverter
	import typeConverter.toSort

	protected val chunkFinder: ChunkFinder[ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshReadVar

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config
	protected val bookkeeper: Bookkeeper

	private var fappCache: Map[Term, Set[Term]] = Map()
	private var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C, tv: TV)
			     (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

		evals2(σ, es, Nil, pve, c, tv)((ts, c1) =>
			Q(ts, c1))

	def evalp(σ: S, p: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			     (Q: (PermissionsTuple, C) => VerificationResult)
           : VerificationResult = {

    assert(p.typ == ast.types.Perm,
           "DefaultEvaluator.evalp expects permission-typed expressions.")

    eval(σ, p, pve, c, tv)((tp, c1) => tp match {
      case fp: FractionalPermissions => Q(fp, c1)
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

		eval2(σ, e, pve, c, tv)((t, c1) => {
//			t.setSrcNode(e)
			Q(t, c1)})
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

	/* Attention: Only use eval(σ, e, m, c Q) inside of internalEval, because
	 *   - eval adds an "Evaluating" operation to the context
	 *   - eval sets the source node of the resulting term
	 */
	private def internalEval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

		/* For debugging only */
		e match {
//			case _: ast.Literal =>
//			case _: Variable =>
//			case _: VariableExpr =>
//			case ThisExpr() =>
			case _ =>
				logger.debug("\nEVALUATING " + e)
				logger.debug(stateFormatter.format(σ))
		}

		e match {
      case ast.True() => Q(True(), c)
      case ast.False() => Q(False(), c)

      case ast.IntegerLiteral(bigval) => Q(IntLiteral(bigval.intValue), c)

      case _: ast.FullPerm => Q(FullPerm(), c)
      case _: ast.NoPerm => Q(NoPerm(), c)

      case v: ast.Variable => Q(σ.γ(v), c)

      case fr: ast.FieldRead =>
        evalFieldRead(σ, fr, pve, c, tv)((fc, c1) =>
          Q(fc.value, c1))

      case ast.Old(e0) => eval(σ \ σ.g, e0, pve, c, tv)(Q)

      case ast.Not(e0) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          Q(Not(t0), c1))

//      case ast.BinaryOp(op, e0, e1) =>
//        op match {
          /* Strict evaluation of AND */
          case ast.And(e0, e1) if config.strictConjunctionEvaluation =>
            evalBinOp(σ, e0, e1, And, pve, c, tv)(Q)

          /* Short-circuiting evaluation of AND */
          case ast.And(e0, e1) =>
            var πPre: Set[Term] = Set()
            var πAux: Set[Term] = Set()

            var t0: Term = True() //.setSrcNode(e0)
            var t1: Term = True() //.setSrcNode(e1)

            eval(σ, e0, pve, c, tv)((_t0, c1) => {
              t0 = _t0
              πPre = decider.π

              decider.pushScope()
              /* TODO: Add a branch-function that only takes a true-continuation.
              *       Give it a more appropriate name, one that expresses
              *       that it is more a continue-if-no-contradiction thing.
              */
              val r =
                branchLocally(t0, c1, tv, LocalAndBranching(e0, t0),
                  (c2: C, tv1: TV) =>
                    eval(σ, e1, pve, c2, tv1)((_t1, c3) => {
                      t1 = _t1
                      πAux = decider.π -- (πPre + t0)
                      Success[C, ST, H, S](c3)}),
                  (c2: C, tv1: TV) => Success[C, ST, H, S](c2))

              decider.popScope()

              r && {
                val tAux = state.terms.utils.BigAnd(πAux)
                assume(tAux, c1)
                Q(And(t0, t1), c1)}})

          /* TODO: Implement a short-circuiting evaluation of OR. */
          case ast.Or(e0, e1) => evalBinOp(σ, e0, e1, Or, pve, c, tv)(Q)

          case ast.Implies(e0, e1) if config.branchOverPureConditionals =>
            eval(σ, e0, pve, c, tv)((t0, c1) =>
              branch(t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
                (c2: C, tv1: TV) => eval(σ, e1, pve, c2, tv1)(Q),
                (c2: C, tv1: TV) => Q(True(), c2)))

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
            var πThen: Set[Term] = Set()
              /* Path conditions assumed while evaluating the consequent */

            var tEvaluatedIf: Term = False()
              /* The term the antecedent actually evaluates too. */
            var tEvaluatedThen: Term = True()
              /* The term the consequent actually evaluates too. */

            decider.pushScope()
            val r =
              eval(σ, e0, pve, c, tv)((t0, c1) => {
                πIf = decider.π -- πPre
                tEvaluatedIf = t0

                branchLocally(t0, c1, tv, LocalImplBranching[ST, H, S](e0, t0),
                  (c2: C, tv1: TV) =>
                    eval(σ, e1, pve, c2, tv1)((t1, c3) => {
                      πThen = decider.π -- (πPre ++ πIf + tEvaluatedIf)
                      tEvaluatedThen = t1
                      Success[C, ST, H, S](c3)}),
                  (c2: C, _) => Success[C, ST, H, S](c2))})

            decider.popScope()

            r && {
              /* The additional path conditions gained while evaluating the
               * antecedent can be assumed in any case.
               * If the antecedent holds, then the additional path conditions
               * related to the consequent can also be assumed.
               */

              val tAuxIf = state.terms.utils.BigAnd(πIf)
              val tAuxThen = state.terms.utils.BigAnd(πThen)
              val tAuxImplies = Implies(tEvaluatedIf, tAuxThen)
              val tImplies = Implies(tEvaluatedIf, tEvaluatedThen)

              assume(Set(tAuxIf, tAuxImplies), c)
              Q(tImplies, c)
            }

//          case ast.Iff() => evalBinOp(σ, e0, e1, Iff, pve, c, tv)(Q)
//        }

      case ast.Ite(e0, e1, e2) if config.branchOverPureConditionals =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c1, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => eval(σ, e1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => eval(σ, e2, pve, c2, tv1)(Q)))

      case ite @ ast.Ite(e0, e1, e2) =>
        val πPre: Set[Term] = decider.π
        var πIf: Option[Set[Term]] = None
        var πThen: Option[Set[Term]] = None
        var πElse: Option[Set[Term]] = None
        var tActualIf: Option[Term] = None
        var tActualThen: Option[Term] = None
        var tActualElse: Option[Term] = None

        decider.pushScope()

        val r =
          eval(σ, e0, pve, c, tv)((t0, c1) => {
            πIf = Some(decider.π -- πPre)
            tActualIf = Some(t0)

            branchLocally(t0, c1, tv, LocalIfBranching[ST, H, S](e0, t0),
              (c2: C, tv1: TV) => {
                eval(σ, e1, pve, c2, tv1)((t1, c3) => {
                  πThen = Some(decider.π -- (πPre ++ πIf.get + t0))
                  tActualThen = Some(t1)
                  Success[C, ST, H, S](c3)})},

              (c2: C, tv1: TV) => {
                eval(σ, e2, pve, c2, tv1)((t2, c3) => {
                  πElse = Some(decider.π -- (πPre ++ πIf.get + Not(t0)))
                  tActualElse = Some(t2)
                  Success[C, ST, H, S](c3)})})})

        decider.popScope()

        r && {
          /* Conjunct all auxilliary terms (sort: bool). */
          val tIf: Term = state.terms.utils.BigAnd(πIf.getOrElse(Set(False())))
          val tThen: Term = state.terms.utils.BigAnd(πThen.getOrElse(Set(True())))
          val tElse: Term = state.terms.utils.BigAnd(πElse.getOrElse(Set(True())))

          /* Ite with auxilliary terms */
          val tIte = Ite(tActualIf.getOrElse(False()), tThen, tElse)

          /* Ite with the actual results of the evaluation */
          val tActualIte =
            Ite(tActualIf.getOrElse(False()),
              tActualThen.getOrElse(fresh("$deadBranch", toSort(e1.typ))),
              tActualElse.getOrElse(fresh("$deadBranch", toSort(e2.typ))))

          assume(Set(tIf, tIte), c)
          Q(tActualIte, c)
        }

      case ast.Equals(e0, e1) => evalBinOp(σ, e0, e1, TermEq, pve, c, tv)(Q)

      /* References */

      case ast.NullLiteral() => Q(Null(), c)

      /* Integers */

      case ast.IntPlus(e0, e1) =>
        evalBinOp(σ, e0, e1, Plus, pve, c, tv)(Q)

      case ast.IntMinus(e0, e1) =>
        evalBinOp(σ, e0, e1, Minus, pve, c, tv)(Q)

      case ast.IntTimes(e0, e1) =>
        evalBinOp(σ, e0, e1, Times, pve, c, tv)(Q)

      case ast.IntDiv(e0, e1) =>
        evalBinOp(σ, e0, e1, Div, pve, c, tv)(Q)

      case ast.IntMod(e0, e1) =>
        evalBinOp(σ, e0, e1, Mod, pve, c, tv)(Q)

      case ast.IntLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c, tv)(Q)

      case ast.IntLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c, tv)(Q)

      case ast.IntGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c, tv)(Q)

      case ast.IntGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c, tv)(Q)

      /* Permissions */

      case ast.ConcPerm(n, d) =>
        Q(ConcPerm(n, d), c)

      case ast.PermPlus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 + t1, pve, c, tv)(Q)

      case ast.PermMinus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 - t1, pve, c, tv)(Q)

      case ast.PermTimes(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 * t1, pve, c, tv)(Q)

      case ast.PermIntTimes(e0, e1) =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          evalp(σ, e1, pve, c1, tv)((t1, c2) =>
            Q(IntPermTimes(t0, t1.combined), c2)))

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
      case ast.DomainFuncApp(func, eArgs) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) =>
          Q(DomainFApp(func.name, tArgs, toSort(func.typ)), c1))

      case quant: ast.Quantified =>
        val body = quant.exp
        val qvar = quant.variable.localVar

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
        var πPost: Set[Term] = πPre
        var tActualBody: Term = True()

        decider.pushScope()

        val tPv = fresh(qvar.name, toSort(qvar.typ))

        val r =
          eval(σ \+ (qvar, tPv), body, pve, c, tv)((tBody, c1) => {
            tActualBody = tBody
            πPost = decider.π
            /* We could call Q directly instead of returning Success, but in
             * that case the path conditions πDelta would also be outside of
             * the quantification. Since they are not needed outside of the
             * quantification we go the extra mile to get ride of them in order
             * to not pollute the path conditions.
             *
             * Actually, only path conditions in which the quantified variable
             * occurrs are waste, others, especially $combine-terms, are actually
             * of interest and should be in the path conditions to avoid the
             * 'fapp-requires-separating-conjunction-fresh-snapshots' problem,
             * which is currently overcome by caching fapp-terms.
             */
            Success[C, ST, H, S](c1)})

        decider.popScope()

        r && {
          val πDelta = πPost -- πPre
          val tAux = state.terms.utils.BigAnd(πDelta)
          val tQuantAux = Quantification(tQuantOp, tPv, tAux)
          val tQuant = Quantification(tQuantOp, tPv, tActualBody)

          assume(tQuantAux, c)
          Q(tQuant, c)}

//      case ast.DomainPredicateExpression(predicate, args) =>
//        predicate match {
//          /* PermissionTerm */
//
//          case ast.PermissionEq =>
//            evalBinOp(σ, args(0), args(1), TermEq, pve, c, tv)(Q)
//
//          case ast.PermissionNeq =>
//            val neq = (t1: Term, t2: Term) => t1 !== t2
//            evalBinOp(σ, args(0), args(1), neq, pve, c, tv)(Q)
//
//          case ast.PermissionAtMost =>
//            evalBinOp(σ, args(0), args(1), AtMost, pve, c, tv)(Q)
//
//          case ast.PermissionLess =>
//            evalBinOp(σ, args(0), args(1), Less, pve, c, tv)(Q)
//
//          case ast.PermissionAtLeast =>
//            evalBinOp(σ, args(0), args(1), AtLeast, pve, c, tv)(Q)
//
//          case ast.PermissionGreater =>
//            evalBinOp(σ, args(0), args(1), Greater, pve, c, tv)(Q)
//
//          /* Booleans */
//
//          case ast.BooleanEvaluate =>
//            eval(σ, args(0), pve, c, tv)(Q)
//
//          /* Domains not directly handled */
//
//          case dp: ast.DomainPredicate =>
//            evals(σ, args, pve, c, tv)((tArgs, c1) =>
//              Q(DomainFApp(dp.fullName, tArgs, sorts.Bool), c1))
//        }

      case fapp @ ast.FuncApp(func, eArgs) =>
//        val BigAnd = ast.utils.collections.BigAnd(func.factory) _
//        val err = (_: ast.Expression) => InvocationFailed(fapp)
        val err = FunctionApplicationFailed(fapp)
        val id = func.name
        /* TODO: We should use something like 'predicate.receiver.dataType + "." + predicate.name'
         *       in order to avoid that different predicates with the same name trigger a cycle
         *       detection.
         */

//        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          evals2(σ, eArgs, Nil, pve, c, tv)((tArgs, c2) => {
//            if (decider.assert(tRcvr !== Null())) {
              bookkeeper.functionApplications += 1
//              val insγ = Γ(   (ast.ThisLiteral()() -> tRcvr)
//                           +: func.formalArgs.map(_.localVar).zip(tArgs))
              val insγ = Γ(func.formalArgs.map(_.localVar).zip(tArgs))
              val σ2 = σ \ insγ
              val pre = ast.utils.BigAnd(func.pres)
              val (rdVar, rdVarConstraints) = freshReadVar("$FAppRd", c2.currentRdPerms)
              val c2a = (c2.setConsumeExactReads(false)
                           .setCurrentRdPerms(ReadPerm(rdVar)))
              assume(rdVarConstraints, c2a)
              consume(σ2, FullPerm(), pre, err, c2a, tv)((_, s, _, c3) => {
//                val tFA = FApp(func, s.convert(sorts.Snap), tRcvr, tArgs, toSort(func.typ))
                val tFA = FApp(func, s.convert(sorts.Snap), tArgs, toSort(func.typ))
                if (fappCache.contains(tFA)) {
                  logger.debug("[Eval(FApp)] Took cache entry for " + fapp)
                  val piFB = fappCache(tFA)
                  assume(piFB, c3)
                  val c3a = (c3.setConsumeExactReads(true)
                               .setCurrentRdPerms(c2.currentRdPerms))
                  Q(tFA, c3a)
                } else {
                  val σ3 = σ2 // \+ (Result, tFA)
                  /* Break recursive cycles */
                  if (c3.cycles(id) < config.unrollFunctions) {
                    val c3a = c3.incCycleCounter(id)
                    val πPre = decider.π
                    val post = ast.utils.BigAnd(func.posts)
                    if (true) {
                      bookkeeper.functionBodyEvaluations += 1
                      eval(σ3, func.exp, pve, c3a, tv)((tFB, c4) =>
                        eval(σ3, post, pve, c4, tv)((tPost, c5) => {
                          val c5a = c5.decCycleCounter(id)
                          val tFAEqFB = tFA === tFB
                          if (config.cacheFunctionApplications)
                            fappCache += (tFA -> (decider.π -- πPre + tFAEqFB + tPost))
                          assume(Set(tFAEqFB, tPost), c5a)
                          val c6 = (c5a.setConsumeExactReads(true)
                                       .setCurrentRdPerms(c2.currentRdPerms))
                          Q(tFA, c6)}))
                    } else {
                      /* Function body is invisible, use postcondition instead */
                        eval(σ3, post, pve, c3a, tv)((tPost, c4) => {
                          val c4a = c4.decCycleCounter(id)
                          if (config.cacheFunctionApplications)
                            fappCache += (tFA -> (decider.π -- πPre + tPost))
                          assume(tPost, c4a)
                          val c5 = (c4a.setConsumeExactReads(true)
                                       .setCurrentRdPerms(c2.currentRdPerms))
                          Q(tFA, c5)})}
                  } else
                    Q(tFA, c3)}})})
//            } else
//              Failure[C, ST, H, S, TV](err dueTo ReceiverNull(eRcvr), c2, tv)}))

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(ast.PredicateLocation(eRcvr, predicate), ePerm),
              eIn) =>

        val body = predicate.body
        val id = predicate.name
          /* TODO: We should use something like 'predicate.receiver.dataType + "." + predicate.name'
           *       in order to avoid that different predicates with the same name trigger a cycle
           *       detection.
           */
        if (c.cycles(predicate.name) < 2 * config.unrollFunctions) {
          val c0a = c.incCycleCounter(id)
          evalp(σ, ePerm, pve, c0a, tv)((tPerm, c1) =>
            if (decider.isNonNegativeFraction(tPerm))
              eval(σ, eRcvr, pve, c1, tv)((tRcvr, c2) =>
//                if (decider.assert(tRcvr !== Null()))
                  consume(σ, FullPerm(), acc, pve, c2, tv)((σ1, snap, _, c3) => {
//                    val insΓ = Γ((ast.ThisLiteral()() -> tRcvr))
                    val insΓ = Γ((predicate.formalArg.localVar -> tRcvr))
                    /* Unfolding only effects the current heap */
                    produce(σ1 \ insΓ, s => snap.convert(s), tPerm, body, pve, c3, tv)((σ2, c4) => {
                      val c4a = c4.decCycleCounter(id)
                      val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
                      eval(σ3, eIn, pve, c4a, tv)(Q)})}))
//                else
//                  Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c2, tv))
            else
              Failure[C, ST, H, S, TV](pve dueTo NegativeFraction(ePerm), c1, tv))}
        else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
                    "P {... && next != null ==> unfolding next.P in e} is currently not " +
                    "supported in Syxc. It should be  possible to wrap 'unfolding next.P in e' " +
                    "in a function, which is then invoked from the predicate body.\n" +
                    "Offending node: " + e)
		}
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

  private def evalPermOp(σ: S,
                         e0: ast.Expression,
                         e1: ast.Expression,
                         permOp: (PermissionsTuple, PermissionsTuple) => PermissionsTuple,
                         pve: PartialVerificationError,
                         c: C,
                         tv: TV)
                        (Q: (PermissionsTuple, C) => VerificationResult)
                        : VerificationResult = {

    evalp(σ, e0, pve, c, tv)((t0, c1) =>
      evalp(σ, e1, pve, c1, tv)((t1, c2) =>
        Q(permOp(t0, t1), c2)))
  }

  private def evalFieldRead(σ: S, fr: ast.FieldRead, pve: PartialVerificationError, c: C, tv: TV)
                           (Q: (FieldChunk, C) => VerificationResult)
                           : VerificationResult = {

    val eRcvr = fr.rcv
    val id = fr.field.name

    eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
      if (decider.assert(tRcvr !== Null())) {
        withChunk[FieldChunk](σ.h, tRcvr, id, eRcvr, pve, c1, tv)(fc =>
          Q(fc, c1))
      } else
        Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))
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
