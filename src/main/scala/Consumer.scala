package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.{MagicWandChunkOutdated, NonPositivePermission, AssertionFalse,
    MagicWandChunkNotFound}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, ChunkIdentifier, StateFactory}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.reporting.TraceView
import interfaces.decider.Decider
import interfaces.state.factoryUtils.Ø
import reporting.{Description, DefaultContext, Consuming, ImplBranching, IfBranching, Bookkeeper}
import state.{SymbolConvert, DirectChunk, DirectFieldChunk, DirectPredicateChunk, MagicWandChunk}
import state.terms._
import state.terms.perms.{IsPositive, IsNoAccess}
import supporters.MagicWandSupporter
import heap.QuantifiedChunkHelper

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
                    with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
									  with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

  protected implicit val manifestH: Manifest[H]

  protected val decider: Decider[P, ST, H, PC, S, C, TV]
  import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val stateUtils: StateUtils[ST, H, PC, S, C, TV]
  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C, TV]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val bookkeeper: Bookkeeper
  protected val config: Config
  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C, TV]

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult = {

    consume(σ, σ.h, p, φ.whenExhaling, pve, c, tv)((h1, t, dcs, c1) => {
      Q(σ \ h1, t, dcs, c1)})
  }

  def consumes(σ: S,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), Nil, Nil, pvef, c, tv)(Q)

  private def consumes(σ: S, h: H, p: P, φs: Seq[ast.Expression], ts: List[Term], dcs: List[DirectChunk], pvef: ast.Expression => PartialVerificationError, c: C, tv: TV)
                       (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    if (φs.isEmpty)
      Q(σ \ h, ts.reverse, dcs.reverse, c)
    else
      consume(σ, h, p, φs.head, pvef(φs.head), c, tv)((h1, t, dcs1, c1) =>
        consumes(σ, h1, p, φs.tail, t :: ts, dcs1 ::: dcs, pvef, c1, tv)(Q))


  protected def consume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                 (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {

    val tv1 = tv.stepInto(c, Consuming[ST, H, S](σ, h, p, φ))

    internalConsume(σ, h, p, φ, pve, c, tv1)((h1, s1, dcs, c1) => {
      tv1.currentStep.σPost = σ \ h1
      Q(h1, s1, dcs, c1)
    })
  }

  private def internalConsume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
                             (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                             : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
      if (c.reserveHeaps.nonEmpty)
        logger.debug("hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
//      c.lhsHeap.map(h => logger.debug("hLHS = " + stateFormatter.format(h)))
    }

		val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c, tv)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1, tv)((h2, s2, dcs2, c2) =>
						Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
        val σC = combine(σ, h, c)
				eval(σC, e0, pve, c, tv)((t0, c1) =>
					branch(σC, t0, c, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => consume(σ, h, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        val σC = combine(σ, h, c)
        eval(σC, e0, pve, c, tv)((t0, c1) =>
          branch(σC, t0, c, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => consume(σ, h, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => consume(σ, h, p, a2, pve, c2, tv1)(Q)))


      /* Quantified field access predicate */
      case ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(locacc @ ast.FieldAccess(eRcvr, f), loss))) =>
        val tVars = vars map (v => decider.fresh(v.name, toSort(v.typ)))
        val γVars = Γ((vars map (v => ast.LocalVariable(v.name)(v.typ))) zip tVars)
        val σ0 = σ \+ γVars

        eval(σ0, cond, pve, c, tv)((tCond, c1) => {
          /* We cheat a bit and syntactically rewrite the range; this should
           * not be needed if the axiomatisation supported it.
           */
          val rewrittenCond = quantifiedChunkHelper.rewriteGuard(tCond)
          if (decider.check(σ0, Not(rewrittenCond)))
            Q(h, Unit, Nil, c1)
          else {
            decider.assume(rewrittenCond)
            eval(σ0, eRcvr, pve, c1, tv)((tRcvr, c2) =>
              evalp(σ0, loss, pve, c2, tv)((tPerm, c3) => {
                val h2 =
                  if (quantifiedChunkHelper.isQuantifiedFor(h,f.name)) h
                  else quantifiedChunkHelper.quantifyChunksForField(h, f.name)
                quantifiedChunkHelper.value(σ, h2, tRcvr, f, pve, locacc, c3, tv)(t => {
                  val ch = quantifiedChunkHelper.transform(tRcvr, f, null, tPerm, /* takes care of rewriting the cond */ tCond)
                  quantifiedChunkHelper.consume(σ, h2, ch, pve, locacc, c3, tv)(h3 => {
                    Q(h3, t, Nil, c3)})})}))}})

      /* Field access predicates for quantified fields */
      case ast.AccessPredicate(locacc @ ast.FieldAccess(eRcvr, field), perm) if quantifiedChunkHelper.isQuantifiedFor(h, field.name) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
            quantifiedChunkHelper.value(σ, h, tRcvr, field, pve, locacc, c2, tv)(t => {
              val ch = quantifiedChunkHelper.transformElement(tRcvr, field.name, null, tPerm)
              quantifiedChunkHelper.consume(σ, h, ch, pve, locacc, c2, tv)(h2 =>
                Q(h2, t, Nil, c2))})))

      case ast.AccessPredicate(locacc, perm) =>
        val σC = combine(σ, h, c)
        withChunkIdentifier(σC, locacc, true, pve, c, tv)((id, c1) =>
          evalp(σC, perm, pve, c1, tv)((tPerm, c2) =>
            decider.assert(σC, IsPositive(tPerm)){
              case true =>
                consumePermissions(σC, h, id, p * tPerm, locacc, pve, c2, tv)((h1, ch, c3, results) =>
                  ch match {
                    case fc: DirectFieldChunk =>
                        val snap = fc.value.convert(sorts.Snap)
                        Q(h1, snap, fc :: Nil, c3)
                    case pc: DirectPredicateChunk =>
                      val h2 =
                        if (results.consumedCompletely)
                          pc.nested.foldLeft(h1){case (ha, nc) => ha - nc}
                        else
                          h1
                      Q(h2, pc.snap, pc :: Nil, c3)
                    case _ => sys.error(s"Unexpected chunk after consuming $φ: $ch")})
              case false =>
                Failure[ST, H, S, TV](pve dueTo NonPositivePermission(perm), tv)}))

      case _: ast.InhaleExhale =>
        Failure[ST, H, S, TV](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(φ), tv)

      /* Handle wands or wand-typed variables, but not general wand-typed
       * expressions. The latter are magic wands wrapped in ghost operations
       * such as packaging, which are handled in the evaluator.
       */
      case _ if φ.typ == ast.types.Wand && magicWandSupporter.isDirectWand(φ) =>
        /* Resolve wand and get mapping from (possibly renamed) local variables to their values. */
        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, φ)
        val σC = combine(σ \+ Γ(wandValues), h, c)

        /* Checks that the value of package-old expressions hasn't changed
         * w.r.t. the state in which the wand was produced.
         *
         * TODO: It would be nice if this method could be moved into the MagicWandSupporter,
         *       but it is not obvious how to call eval(...) from there.
         *       This would be possible if MagicWandSupporter were a trait whose self-type
         *       required it to be mixed into an Evaluator.
         */
        def reinterpret(ch: MagicWandChunk[H], c: C, tv: TV)
                       (Q: C => VerificationResult)
                       : VerificationResult = {

          /* Collect pold-expressions together with conditional guards they are nested in.
           * For example, b ==> pold(e) will be returned as (b, pold(e)).
           */
          val pathConditionedPOlds = magicWandSupporter.pathConditionedPOlds(wand)
          /* Extract e from pold(e) and turn the list of pairs (b, pold(e)) into a list
           * of terms of the shape b && e == pold(e).
           */
          val eqs = pathConditionedPOlds.map{case (pc, po) =>
            val eq = ast.Equals(po.exp, po)(po.pos, po.info)
            ast.Implies(pc, eq)(pc.pos, pc.info)
          }
          val eSame = ast.utils.BigAnd(eqs)
          /* Check the generated equalities. */
          eval(σC, eSame, pve, c/*.copy(poldHeap = Some(ch.hPO))*/, tv)((tSame, c1) =>
            decider.assert(σC, tSame) {
              case true =>
                Q(c1/*.copy(poldHeap = c.poldHeap)*/)
              case false =>
                Failure[ST, H, S, TV](pve dueTo MagicWandChunkOutdated(wand), tv)})
        }

        /* TODO: Getting id by first creating a chunk is not elegant. */
        val id = magicWandSupporter.createChunk(σC.γ, /*σC.h,*/ wand).id

        val hs =
          if (c.exhaleExt) c.reserveHeaps
          else Stack(h)

        magicWandSupporter.doWithMultipleHeaps(hs, c)((h1, c1) =>
          decider.getChunk[MagicWandChunk[H]](σC, h1, id) match {
            case someChunk @ Some(ch) => (someChunk, h1 - ch, c1)
            case _ => (None, h1, c1)
          }
        ){
          case (Some(ch), hs1, c1) =>
            assert(c1.exhaleExt == c.exhaleExt)
            if (c.exhaleExt) {
              /* transfer: move ch into h = σUsed*/
              assert(hs1.size == c.reserveHeaps.size)
              Q(h + ch, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs1))
            } else {
              assert(hs1.size == 1)
              assert(c.reserveHeaps == c1.reserveHeaps)
              Q(hs1.head, decider.fresh(sorts.Snap), List(ch), c1)
            }

//            if (!c.reinterpretWand)
//              Q(hs.head, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs.tail))
//            else
//              reinterpret(ch, c1.copy(reserveHeaps = hs.tail), tv)(c2 =>
//                Q(hs.head, decider.fresh(sorts.Snap), List(ch), c2))
          case _ =>
            Failure[ST, H, S, TV](pve dueTo MagicWandChunkNotFound(wand), tv)
        }

      case pckg @ ast.Packaging(eWand, eIn) =>
        //        val pve = PackagingFailed(pckg)
        /* TODO: Creating a new error reason here will probably yield confusing error
         *       messages if packaging fails as part of exhaling a method's precondition
         *       during a method call.
         *       I expected the error message to be "Packaging ... failed because ... (line N)",
         *       where N denotes the line in which the method precondition can be found.
         *       The message should be "Method ... failed because packaging failed ... because ...
         */
        val σEmp = Σ(σ.γ, Ø, σ.g)
        val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
        decider.locally[(H, Term, List[DirectChunk], C)](QB => {
          produce(σEmp, decider.fresh, FullPerm(), eWand.left, pve, c0, tv.stepInto(c, Description[ST, H, S]("Produce wand lhs")))((σLhs, c1) => {
            val c2 = c1.copy(reserveHeaps = c.reserveHeaps.head :: σLhs.h :: c.reserveHeaps.tail, exhaleExt = true)
            val rhs = eWand.right
            val tv2 = tv.stepInto(c2, Description[ST, H, S]("Consume wand rhs"))
            consume(σEmp, σEmp.h, FullPerm(), rhs, pve, c2, tv2)(scala.Function.untupled(QB))})} /* exhale_ext */
        ){case (_, _, _, c3) => /* result of exhale_ext, h1 = σUsed' */
              /* ??? Producing the wand is not an option because we need to pass in σ.h */
            val ch = magicWandSupporter.createChunk(σ.γ, /*h,*/ eWand)
            val h2 = h + ch /* h2 = σUsed'' */
            val σEmp = Σ(σ.γ, Ø, σ.g)
            val c4 = c3.copy(reserveHeaps = (c3.reserveHeaps.head + h2) :: c3.reserveHeaps.drop(2),
                             exhaleExt = c.exhaleExt)
            consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4, tv)((h3, _, _, c5) =>
              Q(h3, decider.fresh(sorts.Snap), Nil, c5))}

      case ast.Applying(eWand, eIn) =>
        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, eWand)
        val σWV = σ \+ Γ(wandValues)
        val σEmp = Σ(σ.γ, Ø, σ.g)
        val eLHSAndWand = ast.And(wand.left, wand)(wand.left.pos, wand.left.info)
        consume(σEmp \ σWV.γ, h, FullPerm(), eLHSAndWand, pve, c/*.copy(reinterpretWand = false)*/, tv)((h1, _, chs1, c1) => { /* exhale_ext, h1 = σUsed' */
          assert(chs1.last.isInstanceOf[MagicWandChunk[H]], s"Unexpected list of consumed chunks: $chs1")
          val ch = chs1.last.asInstanceOf[MagicWandChunk[H]]
          val c1a = c1.copy(reserveHeaps = Nil, exhaleExt = false)/*.copy(reinterpretWand = c.reinterpretWand)*/
          consume(σWV \ h1, h1, FullPerm(), eLHSAndWand, pve, c1a/*.copy(reinterpretWand = false)*/, tv)((h2, _, chs2, c2) => { /* σUsed'.apply */
            assert(chs2.last.isInstanceOf[MagicWandChunk[H]], s"Unexpected list of consumed chunks: $chs1")
            assert(ch == chs2.last.asInstanceOf[MagicWandChunk[H]], s"Expected $chs1 == $chs2")
            val c2a = c2.copy(lhsHeap = Some(h1))
            produce(σWV \ h2, decider.fresh, FullPerm(), wand.right, pve, c2a, tv)((σ3, c3) => { /* σ3.h = σUsed'' */
              val c3a = c3.copy(reserveHeaps = (c1.reserveHeaps.head + σ3.h) :: c1.reserveHeaps.tail,
                                exhaleExt = c1.exhaleExt,
                                lhsHeap = c2.lhsHeap)
              decider.prover.logComment(s"in consume/apply after producing RHS ${wand.right}}, before consuming $eIn")
              consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c3a, tv)((h4, _, _, c4) =>
                Q(h4, decider.fresh(sorts.Snap), Nil, c4))})})})

      case ast.Folding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) =>

        val predicate = c.program.findPredicate(predicateName)
        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0 = c.incCycleCounter(predicate)
          val σC = combine(σ, h, c0)
          val σEmp = Σ(σ.γ, Ø, σ.g)
          evalp(σC, ePerm, pve, c0, tv)((tPerm, c1) => {
            if (decider.check(σC, IsPositive(tPerm)))
              evals(σC, eArgs, pve, c1, tv)((tArgs, c2) => {
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs) /* TODO: Substitute args in body */
                consume(σEmp \ insγ, h, FullPerm(), predicate.body, pve, c2, tv)((h1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
                  val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false, additionalEvalHeap = Some(c3.reserveHeaps.head))
                  consume(σ \ h1 \ insγ, h1, FullPerm(), predicate.body, pve, c3a, tv)((h2, snap, _, c3b) => { /* σUsed'.fold */
                    produce(σ \ h2, s => snap.convert(s), tPerm, acc, pve, c3b, tv)((σ2, c4) => { /* σ2.h = σUsed'' */
                      val c4a = c4.decCycleCounter(predicate)
                                  .copy(reserveHeaps = (c3.reserveHeaps.head + σ2.h) :: c3.reserveHeaps.tail,
                                        exhaleExt = c3.exhaleExt,
                                        additionalEvalHeap = c3.additionalEvalHeap)
                      consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4a, tv)((h3, _, _, c5) =>
                        Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})})})
            else
              Failure[ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), tv)})
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> folding next.P in e} is currently not " +
            "supported. It should be  possible to wrap 'folding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + φ)

      case ast.Unfolding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) if c.exhaleExt && !φ.isPure =>

        val predicate = c.program.findPredicate(predicateName)
        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0 = c.incCycleCounter(predicate)
          val σC = combine(σ, h, c0)
          val σEmp = Σ(σ.γ, Ø, σ.g)
          evalp(σC, ePerm, pve, c0, tv)((tPerm, c1) =>
            if (decider.check(σC, IsPositive(tPerm)))
              evals(σC, eArgs, pve, c1, tv)((tArgs, c2) =>
                consume(σEmp, h, FullPerm(), acc, pve, c2, tv)((h1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
                  val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false, additionalEvalHeap = Some(c3.reserveHeaps.head))
                  consume(σ \ h1, h1, FullPerm(), acc, pve, c3a, tv)((h2, snap, _, c3b) => { /* σUsed'.unfold */
                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                    produce(σ \ h2 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3b, tv)((σ2, c4) => { /* σ2.h = σUsed'' */ /* TODO: Substitute args in body */
                      val c4a = c4.decCycleCounter(predicate)
                                  .copy(reserveHeaps = (c3.reserveHeaps.head + σ2.h) :: c3.reserveHeaps.tail,
                                        exhaleExt = c3.exhaleExt,
                                        additionalEvalHeap = c3.additionalEvalHeap)
                      consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4a, tv)((h3, _, _, c5) =>
                        Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})}))
            else
              Failure[ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), tv))
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> unfolding next.P in e} is currently not " +
            "supported. It should be  possible to wrap 'unfolding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + φ)

			/* Any regular Expressions, i.e. boolean and arithmetic */
      case _ =>
        val σC = combine(σ, h, c)
        val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
        decider.tryOrFail[(H, Term, List[DirectChunk], C)](σC)((σC1, QS, QF) => {
          eval(σC1, φ, pve, c0, tv)((t, c1) =>
            decider.assert(σC1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c1.copy(reserveHeaps = c.reserveHeaps, exhaleExt = c.exhaleExt)))
              case false =>
                QF(Failure[ST, H, S, TV](pve dueTo AssertionFalse(φ), tv))
            })
        })(Q.tupled)
		}

		consumed
	}

  private def consumePermissions(σ: S,
                                 h: H,
                                 id: ChunkIdentifier,
                                 pLoss: P,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q: (H, DirectChunk, C, PermissionsConsumptionResult) => VerificationResult)
                                : VerificationResult = {

    /* TODO: Integrate into regular, (non-)exact consumption that follows afterwards */
    if (c.exhaleExt) /* Function "transfer" from wands paper */
      /* Permissions are transferred from the stack of heaps to σUsed, which is h in the current context */
      return magicWandSupporter.consumeFromMultipleHeaps(σ, c.reserveHeaps, id, pLoss, locacc, pve, c, tv)((hs, chs, c1/*, pcr*/) => {
        val c2 = c1.copy(reserveHeaps = hs)
        val pcr = PermissionsConsumptionResult(false) // TODO: PermissionsConsumptionResult is bogus!
        Q(h + H(chs), chs.head, c2, pcr)})

    if (consumeExactRead(pLoss, c)) {
      decider.withChunk[DirectChunk](σ, h, id, pLoss, locacc, pve, c, tv)(ch => {
        if (decider.check(σ, IsNoAccess(ch.perm - pLoss))) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      decider.withChunk[DirectChunk](σ, h, id, locacc, pve, c, tv)(ch => {
        assume(pLoss < ch.perm)
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }

  private def consumeExactRead(fp: P, c: C): Boolean = fp match {
    case TermPerm(v: Var) => !c.constrainableARPs.contains(v)
    case _: TermPerm => true
    case _: WildcardPerm => false
    case PermPlus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermMinus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermTimes(t0, t1) => consumeExactRead(t0, c) && consumeExactRead(t1, c)
    case IntPermTimes(_, t1) => consumeExactRead(t1, c)
    case _ => true
  }

  /* TODO: Remove and use DefaultContext.additionalEvalHeap instead.
   *       On the other hand, if additionalEvalHeap is only necessary
   *       to evaluate receivers when executing σUsed'.(un)fold, then it might
   *       be better to do as suggested in the formalisation, that is, to
   *       replace the formal arguments with terms, for example
   *         σUsed'.fold(P(t))
   *       where t := eval(e) if P(e).
   *       */
  private def combine(σ: S, h: H, c: C): S = {
    val hCombined = c.reserveHeaps.headOption.fold(σ.h)(h + _)
    σ \ hCombined
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
