/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.errors.PreconditionInAppFalse
import silver.verifier.reasons.{DivisionByZero, ReceiverNull, NonPositivePermission}
import reporting.{Bookkeeper, DefaultContext}
import interfaces.{Evaluator, Consumer, Producer, VerificationResult, Failure, Success}
import interfaces.state.{ChunkIdentifier, Store, Heap, PathConditions, State, StateFormatter, StateFactory,
    FieldChunk}
import interfaces.decider.Decider
import state.{PredicateChunkIdentifier, FieldChunkIdentifier, SymbolConvert, DirectChunk}
import state.terms._
import state.terms.implicits._
import state.terms.perms.IsPositive
import heap.QuantifiedChunkHelper

trait DefaultEvaluator[
                       ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
											 S <: State[ST, H, S]]
		extends Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext] with HasLocalState
		{ this: Logging with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext]
										with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext]
										with Brancher[ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val symbolConverter: SymbolConvert
	import symbolConverter.toSort

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config
	protected val bookkeeper: Bookkeeper

  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C]

	/*private*/ var fappCache: Map[Term, Set[Term]] = Map()
	/*private*/ var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()
  /*private*/ var quantifiedVars: Stack[Term] = Stack()

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C)
			     (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

		evals2(σ, es, Nil, pve, c)((ts, c1) =>
			Q(ts, c1))

	def evalp(σ: S, p: ast.Expression, pve: PartialVerificationError, c: C)
			     (Q: (P, C) => VerificationResult)
           : VerificationResult = {

    eval(σ, p, pve, c)((tp, c1) => tp match {
      case fp: DefaultFractionalPermissions => Q(fp, c1)
      case _ => Q(TermPerm(tp), c1)})
  }

	private def evals2(σ: S,
                     es: Seq[ast.Expression],
                     ts: List[Term],
                     pve: PartialVerificationError,
                     c: C)
                    (Q: (List[Term], C) => VerificationResult)
                    : VerificationResult = {

		if (es.isEmpty)
			Q(ts.reverse, c)
		else
			eval(σ, es.head, pve, c)((t, c1) =>
				evals2(σ, es.tail, t :: ts, pve, c1)(Q))
	}

	def eval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {

		eval2(σ, e, pve, c)((t, c1) =>
			Q(t, c1))
  }

  protected def eval2(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

    internalEval(σ, e, pve, c)((t, c1) => {
      Q(t, c1)
    })
  }

	/* Attention: Only use eval(σ, e, m, c)(Q) inside of internalEval, because
	 *   - eval adds an "Evaluating" operation to the context
	 *   - eval sets the source node of the resulting term
	 */
	private def internalEval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
                          (Q: (Term, C) => VerificationResult)
                          : VerificationResult = {

		/* For debugging only */
		e match {
			case  _: ast.True | _: ast.False | _: ast.NullLiteral | _: ast.IntegerLiteral | _: ast.FullPerm | _: ast.NoPerm
          | _: ast.Variable | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.ResultLiteral
          | _: ast.WildcardPerm | _: ast.FieldAccess =>

			case _ =>
        logger.debug(s"\nEVAL ${e.pos}: $e")
				logger.debug(stateFormatter.format(σ))
        decider.prover.logComment(s"[eval] $e")
		}

    /* Since commit 0cf1f26, evaluating unfoldings is a local operation, and it
     * might be tempting to think that we don't need to locally evaluate
     * Implies and Ite anymore. However, that is not true, because not all of
     * them occur in the context of an unfolding. They can also occur in a
     * pre/postcondition such as 'requires b1 ==> b2', in which case Silicon
     * still shouldn't branch.
     */

    /* TODO: LocalEvaluationResults collect contexts as well.
     *       However, only one context can be passed on to Q, and currently
     *       the one from the first LocalEvaluationResult is taken.
     *       This shouldn't be much of a problem, except maybe for debugging,
     *       as long as the context doesn't keep track of any crucial
     *       information. This may not always be the case, however. E.g., the
     *       Wands-Silicon prototype (for the rejected FM'14 paper) uses the
     *       context to record the reserve heap.
     */

    val resultTerm = e match {
      case ast.True() => Q(True(), c)
      case ast.False() => Q(False(), c)

      case ast.NullLiteral() => Q(Null(), c)
      case ast.IntegerLiteral(bigval) => Q(IntLiteral(bigval), c)

      case ast.Equals(e0, e1) => evalBinOp(σ, e0, e1, (p0: Term, p1: Term) => Eq(p0, p1, true), pve, c)(Q)
      case ast.Unequals(e0, e1) => evalBinOp(σ, e0, e1, (p0: Term, p1: Term) => Not(Eq(p0, p1)), pve, c)(Q)

      case v: ast.Variable => Q(σ.γ(v), c)

      case _: ast.FullPerm => Q(FullPerm(), c)
      case _: ast.NoPerm => Q(NoPerm(), c)

      case ast.FractionalPerm(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => FractionPerm(t0, t1), pve, c)((tFP, c1) =>
          failIfDivByZero(σ, tFP, e1, tFP.d, TermPerm(0), pve, c1)(Q))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = stateUtils.freshARP()
        assume(tConstraints)
        Q(WildcardPerm(tVar), c)

      case ast.CurrentPerm(locacc) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          decider.getChunk[DirectChunk](σ, σ.h, id) match {
            case Some(ch) => Q(ch.perm, c1)
            case None => Q(NoPerm(), c1)
          })

      /* Field access if the heap is quantified for that field */
      case fa: ast.FieldAccess if quantifiedChunkHelper.isQuantifiedFor(σ.h, fa.field.name) =>
        val ch = quantifiedChunkHelper.getQuantifiedChunk(σ.h, fa.field.name).get // TODO: Slightly inefficient, since it repeats the work of isQuantifiedFor
        eval(σ, fa.rcv, pve, c)((tRcvr, c1) =>
          quantifiedChunkHelper.value(σ, σ.h, tRcvr, fa.field, ch.quantifiedVars, pve, fa, c)((t) => {
            Q(t, c1)}))

      case fa: ast.FieldAccess =>
        withChunkIdentifier(σ, fa, true, pve, c)((id, c1) =>
          decider.withChunk[FieldChunk](σ, σ.h, id, fa, pve, c1)(ch =>
            Q(ch.value, c1)))

      case ast.Not(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Not(t0), c1))

      case ast.IntNeg(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Minus(0, t0), c1))

      case ast.Old(e0) => eval(σ \ σ.g, e0, pve, c)(Q)

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, And, pve, c)(Q)

      /* Short-circuiting evaluation of AND */
      case ast.And(e0, e1) =>
        /* TODO: It should no longer be possible to accumulate local results, because
         *       all branching constructs are locally evaluated themselves.
         *       Hence, implement evaluation of AND similar to that of OR.
         *       Try to reuse code!
         */
        var πPre: Set[Term] = Set()
        var t0: Option[Term] = None
        var localResults: List[LocalEvaluationResult] = Nil

        eval(σ, e0, pve, c)((_t0, c1) => {
          assert(t0.isEmpty || t0.get == _t0, s"Unexpected difference: $t0 vs ${_t0}")

          t0 = Some(_t0)
          πPre = decider.π

          decider.pushScope()
          /* TODO: Add a branch-function that only takes a true-continuation.
          *       Give it a more appropriate name, one that expresses
          *       that it is more a continue-if-no-contradiction thing.
          */
          val r =
            branch(σ, t0.get, c1,
              (c2: C) =>
                eval(σ, e1, pve, c2)((_t1, c3) => {
                  localResults ::= LocalEvaluationResult(guards, _t1, decider.π -- (πPre + t0.get), c3)
                  Success()}),
              (c2: C) => Success())

          decider.popScope()

          r && {
            val (t1: Term, tAux: Set[Term]) = combine(localResults)
            val tAnd = And(t0.get, t1)
            assume(tAux)
            Q(tAnd, localResults.headOption.fold(c1)(_.context))}})

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, Or, pve, c)(Q)

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

        eval(σ, e0, pve, c)((_t0, c1) => {
          assert(t0.isEmpty, s"Unexpected branching occurred while locally evaluating $e0")
          t0 = Some(_t0)
          πPre = decider.π

          decider.pushScope()
          /* TODO: See comment to short-circuiting evaluation of AND */
          val t0Neg = Not(t0.get)
          val r =
            branch(σ, t0Neg, c1,
              (c2: C) =>
                eval(σ, e1, pve, c2)((_t1, c3) => {
                  assert(t1.isEmpty, s"Unexpected branching occurred while locally evaluating $e1")
                  t1 = Some(_t1)
                  πt1 = decider.π -- (πPre + t0Neg) /* Removing t0Neg from πt1 is crucial! */
                  Success()}),
              (c2: C) => Success())
          decider.popScope()

          r && {
            val tAux = state.terms.utils.BigAnd(πt1)
            val tOr = Or(t0.get, t1.getOrElse(True()))
            assume(tAux)
            Q(tOr, c1)}})

      case _: ast.Implies if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c)(Q)

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
          eval(σ, e0, pve, c)((t0, c1) => {
            val πDiff = decider.π -- πPre

            assert(tEvaluatedIf == False() || tEvaluatedIf == t0, s"Unexpected difference: $tEvaluatedIf vs $t0")
            assert(πIf.isEmpty || πIf == πDiff, s"Unexpected difference: $πIf vs $πDiff")

            πIf = πDiff
            tEvaluatedIf = t0

            branch(σ, t0, c1,
              (c2: C) =>
                eval(σ, e1, pve, c2)((t1, c3) => {
                  localResults ::= LocalEvaluationResult(guards, t1, decider.π -- (πPre ++ πIf + tEvaluatedIf), c3)
                  Success()}),
              (c2: C) => Success())})

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
          Q(tImplies, localResults.headOption.fold(c)(_.context))}

      case _: ast.Ite if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c)(Q)

      case ite @ ast.Ite(e0, e1, e2) =>
        val πPre: Set[Term] = decider.π
        var πIf: Option[Set[Term]] = None
        var tActualIf: Option[Term] = None

        var localResultsThen: List[LocalEvaluationResult] = Nil
        var localResultsElse: List[LocalEvaluationResult] = Nil

        decider.pushScope()

        val r =
          eval(σ, e0, pve, c)((t0, c1) => {
            val πDiff = decider.π -- πPre

            assert(tActualIf.isEmpty || tActualIf.get == t0, s"Unexpected difference: $tActualIf vs $t0")
            assert(πIf.isEmpty || πIf.get == πDiff, s"Unexpected difference: $πIf vs $πDiff")

            πIf = Some(πDiff)
            tActualIf = Some(t0)

            branch(σ, t0, c1,
              (c2: C) => {
                eval(σ, e1, pve, c2)((t1, c3) => {
                  localResultsThen ::= LocalEvaluationResult(guards, t1, decider.π -- (πPre ++ πIf.get + t0), c3)
                  Success()})},
              (c2: C) => {
                eval(σ, e2, pve, c2)((t2, c3) => {
                  localResultsElse ::= LocalEvaluationResult(guards, t2, decider.π -- (πPre ++ πIf.get + Not(t0)), c3)
                  Success()})})})

        decider.popScope()

        val localResults = localResultsThen ::: localResultsElse

        r && {
          /* Conjunct all auxiliary terms (sort: bool). */
          val tAuxIf: Term = state.terms.utils.BigAnd(πIf.getOrElse(Set(False())))

          val quantifiedVarsSorts = quantifiedVars.map(_.sort)
          val actualThenFuncSort = sorts.Arrow(quantifiedVarsSorts, toSort(e1.typ))
          val actualElseFuncSort = sorts.Arrow(quantifiedVarsSorts, toSort(e2.typ))

          val tActualThenVar = Apply(fresh("actualThen", actualThenFuncSort), quantifiedVars)
          val tActualElseVar = Apply(fresh("actualElse", actualElseFuncSort), quantifiedVars)

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
                if (localResultsThen.nonEmpty) tActualThenVar
                else Apply(fresh("$deadThen", actualThenFuncSort), quantifiedVars),
                if (localResultsElse.nonEmpty) tActualElseVar
                else Apply(fresh("$deadElse", actualElseFuncSort), quantifiedVars))

          val actualTerms = And(tActualThen, tActualElse)

          assume(Set(tAuxIf, tAuxIte, actualTerms))
          Q(tActualIte, localResults.headOption.fold(c)(_.context))}

      /* Integers */

      case ast.IntPlus(e0, e1) =>
        evalBinOp(σ, e0, e1, Plus, pve, c)(Q)

      case ast.IntMinus(e0, e1) =>
        evalBinOp(σ, e0, e1, Minus, pve, c)(Q)

      case ast.IntTimes(e0, e1) =>
        evalBinOp(σ, e0, e1, Times, pve, c)(Q)

      case ast.IntDiv(e0, e1) =>
        evalBinOp(σ, e0, e1, Div, pve, c)((tDiv, c1) =>
          failIfDivByZero(σ, tDiv, e1, tDiv.p1, 0, pve, c1)(Q))

      case ast.IntMod(e0, e1) =>
        evalBinOp(σ, e0, e1, Mod, pve, c)((tMod, c1) =>
          failIfDivByZero(σ, tMod, e1, tMod.p1, 0, pve, c1)(Q))

      case ast.IntLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.IntLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.IntGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.IntGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Permissions */

      case ast.PermPlus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 + t1, pve, c)(Q)

      case ast.PermMinus(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 - t1, pve, c)(Q)

      case ast.PermTimes(e0, e1) =>
        evalPermOp(σ, e0, e1, (t0, t1) => t0 * t1, pve, c)(Q)

      case ast.IntPermTimes(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          evalp(σ, e1, pve, c1)((t1, c2) =>
            Q(IntPermTimes(t0, t1), c2)))

      case ast.PermLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.PermLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.PermGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.PermGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evals(σ, eArgs, pve, c)((tArgs, c1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = toSort(dfa.typ)
          val fi = symbolConverter.toFunction(c.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(DomainFApp(fi, tArgs), c1)})

      case _: ast.Quantified if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c)(Q)

      case quant: ast.Quantified =>
        val (triggerQuant, tQuantOp, silTriggers) = quant match {
          case fa: ast.Forall => (fa.autoTrigger, Forall, fa.autoTrigger.triggers)
          case ex: ast.Exists => (ex, Exists, Seq())
        }

        val body = triggerQuant.exp
        val vars = triggerQuant.variables map (_.localVar)

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
         */

        val πPre: Set[Term] = decider.π
        var localResults: List[LocalEvaluationResult] = Nil
        var triggers: List[Trigger] = Nil

        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ(vars zip tVars)
        val σQuant = σ \+ γVars

        decider.pushScope()
        quantifiedVars = tVars ++: quantifiedVars

        val r =
          evalTriggers(σQuant, silTriggers, pve, c)((_triggers, c1) =>
            eval(σQuant, body, pve, c1)((tBody, c2) => {
              triggers = _triggers
              localResults ::= LocalEvaluationResult(guards, tBody, decider.π -- πPre, c2)

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
              Success()}))

        quantifiedVars = quantifiedVars.drop(tVars.length)
        decider.popScope()

        r && {
          val (tActual: Term, tAux: Set[Term]) = combine(localResults)
          /* TODO: Translate SIL triggers as well */
          val tQuantAux = Quantification(tQuantOp, tVars, state.terms.utils.BigAnd(tAux), triggers)
          val tQuant = Quantification(tQuantOp, tVars, tActual, triggers)
          assume(tQuantAux)
          Q(tQuant, localResults.headOption.fold(c)(_.context))}

      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val err = PreconditionInAppFalse(fapp)
        val func = c.program.findFunction(funcName)

        evals2(σ, eArgs, Nil, pve, c)((tArgs, c2) => {
          bookkeeper.functionApplications += 1
          val insγ = Γ(func.formalArgs.map(_.localVar).zip(tArgs))
          val σ2 = σ \ insγ
          val pre = ast.utils.BigAnd(func.pres)
          consume(σ2, FullPerm(), pre, err, c2)((_, s, _, c3) => {
            val tFA = FApp(symbolConverter.toFunction(func), s.convert(sorts.Snap), tArgs)
            if (fappCache.contains(tFA)) {
              val piFB = fappCache(tFA)
              assume(piFB)
              Q(tFA, c3)
            } else {
              val σ3 = σ2 \+ (func.result, tFA)
              val πPre = decider.π
              val post = ast.utils.BigAnd(func.posts)
              /* Break recursive cycles */
              if (c3.cycles(func) < config.unrollFunctions()) {
                val c3a = c3.incCycleCounter(func)
                bookkeeper.functionBodyEvaluations += 1
                eval(σ3, func.exp, pve, c3a)((tFB, c4) =>
                  eval(σ3, post, pve, c4)((tPost, c5) => {
                    val c5a = c5.decCycleCounter(func)
                    val tFAEqFB = Implies(state.terms.utils.BigAnd(guards), tFA === tFB)
                    if (!config.disableFunctionApplicationCaching())
                      fappCache += (tFA -> (decider.π -- πPre + tFAEqFB + tPost))
                    assume(Set(tFAEqFB, tPost))
                    Q(tFA, c5a)}))
              } else {
                /* Unfolded the function often enough already. We still need to
                 * evaluate the postcondition, though, because Z3 might
                 * otherwise not know enough about the recursive call.
                 * For example, that the length of a list is always positive.
                 */
                eval(σ3, post, pve, c3)((tPost, c4) => {
                  if (!config.disableFunctionApplicationCaching())
                    fappCache += (tFA -> (decider.π -- πPre + tPost))
                  assume(tPost)
                  Q(tFA, c4)})}}})})

      case _: ast.Unfolding if config.disableLocalEvaluations() => nonLocalEval(σ, e, pve, c)(Q)

      case ast.Unfolding(
                acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                eIn) =>

        val predicate = c.program.findPredicate(predicateName)

        /* Unfolding only has a temporary effect on the current heap because
         * the resulting heap is not forwarded to the final continuation.
         */

        var πPre: Set[Term] = Set()
        var tPerm: Option[Term] = None
        var localResults: List[LocalEvaluationResult] = Nil

        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0a = c.incCycleCounter(predicate)

          val r =
            evalp(σ, ePerm, pve, c0a)((_tPerm, c1) => {
              assert(tPerm.isEmpty || tPerm.get == _tPerm, s"Unexpected difference: $tPerm vs ${_tPerm}")
              tPerm = Some(_tPerm)
              πPre = decider.π
              decider.assert(σ, IsPositive(_tPerm)){
                case true =>
                  evals(σ, eArgs, pve, c1)((tArgs, c2) =>
                    consume(σ, FullPerm(), acc, pve, c2)((σ1, snap, _, c3) => {
                      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                      produce(σ1 \ insγ, s => snap.convert(s), _tPerm, predicate.body, pve, c3)((σ2, c4) => {
                        val c4a = c4.decCycleCounter(predicate)
                        val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
                        eval(σ3, eIn, pve, c4a)((tIn, c5) => {
                          localResults ::= LocalEvaluationResult(guards, tIn, decider.π -- πPre, c5)
                          Success()})})}))
                case false =>
                  Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm))}})

          r && {
            val quantifiedVarsSorts = quantifiedVars.map(_.sort)
            val actualInFuncSort = sorts.Arrow(quantifiedVarsSorts, toSort(eIn.typ))
            val tActualInVar = Apply(fresh("actualIn", actualInFuncSort), quantifiedVars)
            val (tActualIn: Term, tAuxIn: Set[Term]) = combine(localResults, tActualInVar === _)
              /* TODO: See comment about performance in case ast.Ite */
            assume(tAuxIn + tActualIn)
            Q(tActualInVar, localResults.headOption.fold(c)(_.context))}
        } else
          Failure[ST, H, S](ast.Consistency.createUnsupportedPredicateRecursionError(e))

      /* Sequences */

      case ast.SeqIn(e0, e1) => evalBinOp(σ, e1, e0, SeqIn, pve, c)(Q)
        /* Note the reversed order of the arguments! */

      case silver.ast.SeqAppend(e0, e1) => evalBinOp(σ, e0, e1, SeqAppend, pve, c)(Q)
      case silver.ast.SeqDrop(e0, e1) => evalBinOp(σ, e0, e1, SeqDrop, pve, c)(Q)
      case silver.ast.SeqTake(e0, e1) => evalBinOp(σ, e0, e1, SeqTake, pve, c)(Q)
      case ast.SeqAt(e0, e1) => evalBinOp(σ, e0, e1, SeqAt, pve, c)(Q)
      case silver.ast.SeqLength(e0) => eval(σ, e0, pve, c)((t0, c1) => Q(SeqLength(t0), c1))
      case silver.ast.EmptySeq(typ) => Q(SeqNil(toSort(typ)), c)
      case ast.SeqRanged(e0, e1) => evalBinOp(σ, e0, e1, SeqRanged, pve, c)(Q)

      case silver.ast.SeqUpdate(e0, e1, e2) =>
        evals2(σ, List(e0, e1, e2), Nil, pve, c)((ts, c1) =>
          Q(SeqUpdate(ts(0), ts(1), ts(2)), c1))

      case silver.ast.ExplicitSeq(es) =>
        evals2(σ, es.reverse, Nil, pve, c)((tEs, c1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(SeqSingleton(te), tSeq))
          assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(tSeq, c1)})

      /* Sets and multisets */

      case silver.ast.EmptySet(typ) => Q(EmptySet(toSort(typ)), c)
      case silver.ast.EmptyMultiset(typ) => Q(EmptyMultiset(toSort(typ)), c)

      case silver.ast.ExplicitSet(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(tSet, c1)})

      case silver.ast.ExplicitMultiset(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(tMultiset, c1)})

      case silver.ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetUnion, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetUnion, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIntersection, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIntersection, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetSubset, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetSubset, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetDifference, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetDifference, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIn, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIn, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.types.Set => eval(σ, e0, pve, c)((t0, c1) => Q(SetCardinality(t0), c1))
        case _: ast.types.Multiset => eval(σ, e0, pve, c)((t0, c1) => Q(MultisetCardinality(t0), c1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(e))
		}

    resultTerm
	}

  /* The non-local evaluations are intended for benchmarking and debugging
   * only, because they can result in incompletenesses (and probably also
   * in unsoundnesses because they are not constantly tested).
   */
  private def nonLocalEval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
                          (Q: (Term, C) => VerificationResult)
                          : VerificationResult = {

    assert(config.disableLocalEvaluations(),
           "Unexpected call to performNonLocalEvaluation since config.localEvaluations is true.")

    e match {
      case ast.Implies(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => eval(σ, e1, pve, c2)(Q),
            (c2: C) => Q(True(), c2)))

      case ast.Ite(e0, e1, e2) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => eval(σ, e1, pve, c2)(Q),
            (c2: C) => eval(σ, e2, pve, c2)(Q)))

      case ast.Unfolding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm), eIn) =>
        val predicate = c.program.findPredicate(predicateName)

        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0a = c.incCycleCounter(predicate)
          evalp(σ, ePerm, pve, c0a)((tPerm, c1) =>
            decider.assert(σ, IsPositive(tPerm)){
              case true =>
                evals(σ, eArgs, pve, c1)((tArgs, c2) =>
                  consume(σ, FullPerm(), acc, pve, c2)((σ1, snap, _, c3) => {
                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                    /* Unfolding only effects the current heap */
                    produce(σ1 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3)((σ2, c4) => {
                      val c4a = c4.decCycleCounter(predicate)
                      val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
                      eval(σ3, eIn, pve, c4a)(Q)})}))
              case false =>
                Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm))})}
        else
          Failure[ST, H, S](ast.Consistency.createUnsupportedPredicateRecursionError(e))

      case quant: ast.Quantified if config.disableLocalEvaluations() =>
        val body = quant.exp
        val vars = quant.variables map (_.localVar)

        val (tQuantOp, silTriggers) = quant match {
          case fa: ast.Forall => (Forall, fa.autoTrigger.triggers)
          case _: ast.Exists => (Exists, Seq())
        }

        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ(vars zip tVars)
        val σQuant = σ \+ γVars

        val πPre: Set[Term] = decider.π
        evalTriggers(σQuant, silTriggers, pve, c)((triggers, c1) =>
          eval(σQuant, body, pve, c1)((tBody, c2) => {
            val (tActual: Term, tAux: Set[Term]) =
              combine(LocalEvaluationResult(guards, tBody, decider.π -- πPre, c2) :: Nil)
            val tQuantAux = Quantification(tQuantOp, tVars, state.terms.utils.BigAnd(tAux), triggers)
            val tQuant = Quantification(tQuantOp, tVars, tActual, triggers)
            assume(tQuantAux)
            Q(tQuant, c2)
          }))

      case _ => sys.error(s"Cannot non-locally evaluate $e (${e.getClass.getName})")
    }
  }

  def withChunkIdentifier(σ: S,
                          locacc: ast.LocationAccess,
                          assertRcvrNonNull: Boolean,
                          pve: PartialVerificationError,
                          c: C)
                         (Q: (ChunkIdentifier, C) => VerificationResult)
                         : VerificationResult =

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          if (assertRcvrNonNull)
            decider.assert(σ, Or(NullTrigger(tRcvr), tRcvr !== Null())){
              case true => Q(FieldChunkIdentifier(tRcvr, field.name), c1)
              case false => Failure[ST, H, S](pve dueTo ReceiverNull(locacc))}
          else
            Q(FieldChunkIdentifier(tRcvr, field.name), c1))

      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
          Q(PredicateChunkIdentifier(predicateName, tArgs), c1))
    }

	private def evalBinOp[T <: Term]
                       (σ: S,
			                  e0: ast.Expression,
                        e1: ast.Expression,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
			                  c: C)
                       (Q: (T, C) => VerificationResult)
                       : VerificationResult = {

		eval(σ, e0, pve, c)((t0, c1) =>
			eval(σ, e1, pve, c1)((t1, c2) =>
				Q(termOp(t0, t1), c2)))
  }

  private def failIfDivByZero(σ: S,
                              t: Term,
                              eDivisor: ast.Expression,
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              c: C)
                             (Q: (Term, C) => VerificationResult)
                             : VerificationResult = {

    decider.assert(σ, tDivisor !== tZero){
      case true => Q(t, c)
      case false => Failure[ST, H, S](pve dueTo DivisionByZero(eDivisor))
    }
  }

  private def evalPermOp[PO <: P]
                        (σ: S,
                         e0: ast.Expression,
                         e1: ast.Expression,
                         permOp: (P, P) => PO,
                         pve: PartialVerificationError,
                         c: C)
                        (Q: (PO, C) => VerificationResult)
                        : VerificationResult = {

    evalp(σ, e0, pve, c)((t0, c1) =>
      evalp(σ, e1, pve, c1)((t1, c2) =>
        Q(permOp(t0, t1), c2)))
  }

  private case class LocalEvaluationResult(πGuards: Seq[Term],
                                           actualResult: Term,
                                           auxiliaryTerms: Set[Term],
                                           context: C)

  private def combine(localResults: Seq[LocalEvaluationResult],
                      actualResultTransformer: Term => Term = Predef.identity)
                     : (Term, Set[Term]) = {

    val (t1: Term, tAux: Set[Term]) =
      localResults.map {lr =>
        val newGuards = lr.πGuards filterNot decider.π.contains
        val guard: Term = state.terms.utils.BigAnd(newGuards)
        val tAct: Term = Implies(guard, actualResultTransformer(lr.actualResult))
        val tAux: Term = Implies(guard, state.terms.utils.BigAnd(lr.auxiliaryTerms))

        (tAct, tAux)
      }.foldLeft((True(): Term, Set[Term]())){case ((tActAcc, tAuxAcc), (tAct, _tAux)) =>
        (And(tActAcc, tAct), tAuxAcc + _tAux)
      }

    (t1, tAux)
  }

  /* TODO: The CP-style in which Silicon's main components are written makes it hard to work
   *       with sequences. evalTriggers, evals and execs all share the same pattern, they
   *       essentially recurse over a sequence and accumulate results, where results can be
   *       terms, verification results, contexts, or any combination of these.
   *       It would be nice to find a (probably crazy functional) abstraction that avoids
   *       having to implement that pattern over and over again.
   *
   */
  private def evalTriggers(σ: S, silTriggers: Seq[ast.Trigger], pve: PartialVerificationError, c: C)
                          (Q: (List[Trigger], C) => VerificationResult)
                          : VerificationResult =

    evalTriggers(σ, silTriggers, Nil, pve, c)(Q)

  private def evalTriggers(σ: S,
                           silTriggers: Seq[ast.Trigger],
                           triggers: List[Trigger],
                           pve: PartialVerificationError,
                           c: C)
                          (Q: (List[Trigger], C) => VerificationResult)
                          : VerificationResult = {

    if (silTriggers.isEmpty)
      Q(triggers.reverse, c)
    else
      evalTrigger(σ, silTriggers.head, pve, c)((t, c1) =>
        evalTriggers(σ, silTriggers.tail, t :: triggers, pve, c1)(Q))
  }

  /* TODO: Support applications of user-provided functions as triggers as well.
   *       We can use eval for this, but we don't want to evaluate the function
   *       body as well. Moreover, we don't need to check the preconditions
   *       of functions used as triggers, but we do need to compute the snapshot,
   *       because it is part of terms.FApp.
   *       Axiomatising functions could make this task easier, and it is thus
   *       probably not worth to address this problem before function
   *       axiomatisation has been implemented (or discarded as an idea).
   */
  private def evalTrigger(σ: S, trigger: ast.Trigger, pve: PartialVerificationError, c: C)
                         (Q: (Trigger, C) => VerificationResult)
                         : VerificationResult = {

    val es =
      trigger.exps.map {
        case ast.Old(e) => e
        case e => e
      }.flatMap {
        case _: ast.FuncApp => None
        case f: silver.ast.PossibleTrigger => Some(f)
        case _ => None
      }

    if (es.length != trigger.exps.length)
      logger.warn(s"Only domain function applications are currently supported as triggers. Found ${trigger.exps}")
    evals2(σ, es, Nil, pve, c)((ts, c1) =>
      Q(Trigger(ts), c1))
  }


	override def pushLocalState() {
		fappCacheFrames = fappCache :: fappCacheFrames
		super.pushLocalState()
	}

	override def popLocalState() {
		fappCache = fappCacheFrames.head
		fappCacheFrames = fappCacheFrames.tail
		super.popLocalState()
	}
}
