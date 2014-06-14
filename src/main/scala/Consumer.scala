package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.{MagicWandChunkOutdated, InsufficientPermission, NonPositivePermission, AssertionFalse,
    MagicWandChunkNotFound}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, ChunkIdentifier, StateFactory}
import interfaces.{Success, Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.reporting.TraceView
import interfaces.decider.Decider
import interfaces.state.factoryUtils.Ø
import reporting.{Description, DefaultContext, Consuming, ImplBranching, IfBranching, Bookkeeper}
import state.{SymbolConvert, DirectChunk, DirectFieldChunk, DirectPredicateChunk, MagicWandChunk}
import state.terms._
import state.terms.perms.{IsPositive, IsNoAccess, IsAsPermissive}
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

    /* TODO: What should the result of current-perms(x.f) be when it occurs on the rhs of a magic wand? */

//    val c0 = c.copy(reserveEvalHeap = c.reserveHeap)
    val c0 = c // c.copy(reserveEvalHeaps = c.reserveHeaps)

    consume(σ, σ.h, p, φ.whenExhaling, pve, c0, tv)((h1, t, dcs, c1) => {
      val c2 = c1 // c1.copy(reserveEvalHeaps = c.reserveEvalHeaps)
      Q(σ \ h1, t, dcs, c2)})
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
      if (c.reserveHeaps.nonEmpty) {
        logger.debug("hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
//        logger.debug("hRE = " + c.reserveEvalHeaps.map(stateFormatter.format).mkString("", ",\n      ", ""))
      }
    }

		val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c, tv)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1, tv)((h2, s2, dcs2, c2) =>
						Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c, tv)((t0, c1) =>
					branch(σ, t0, c, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => consume(σ, h, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(σ, t0, c, tv, IfBranching[ST, H, S](e0, t0),
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
//                    println("\n[consumer/forall]")
//                    println(s"  t = $t")
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
        withChunkIdentifier(σ, locacc, true, pve, c, tv)((id, c1) =>
          evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
            decider.assert(σ, IsPositive(tPerm)){
              case true =>
                consumePermissions(σ, h, id, p * tPerm, locacc, pve, c2, tv)((h1, ch, c3, results) =>
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
        val σ0 = σ \+ Γ(wandValues)

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
          eval(σ0, eSame, pve, c.copy(poldHeap = Some(ch.hPO)), tv)((tSame, c1) =>
            decider.assert(σ, tSame) {
              case true =>
                Q(c1.copy(poldHeap = c.poldHeap))
              case false =>
                Failure[ST, H, S, TV](pve dueTo MagicWandChunkOutdated(wand), tv)})
        }

        /* TODO: Getting id by first creating a chunk is not elegant. */
        val id = magicWandSupporter.createChunk(σ0.γ, σ0.h, wand).id

        magicWandSupporter.doWithMultipleHeaps(σ0, h :: c.reserveHeaps, c)((σ1, h1, c1) =>
          decider.getChunk[MagicWandChunk[H]](σ1, h1, id) match {
            case someChunk @ Some(ch) => (someChunk, h1 - ch, c1)
            case _ => (None, h1, c1)
          }
        ){
          case (Some(ch), hs, c1) =>
            if (!c.reinterpretWand)
              Q(hs.head, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs.tail))
            else
              reinterpret(ch, c1.copy(reserveHeaps = hs.tail), tv)(c2 =>
                Q(hs.head, decider.fresh(sorts.Snap), List(ch), c2))
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
        val σ0 = Σ(σ.γ, Ø, σ.g)
        val c0 = c.copy(poldHeap = Some(σ.h))
        produce(σ0, decider.fresh, FullPerm(), eWand.left, pve, c0, tv.stepInto(c, Description[ST, H, S]("Produce wand lhs")))((σLhs, c1) => {
          val c2 = c1.copy(reserveHeaps = h :: c1.reserveHeaps,
                           givenHeap = Some(σLhs.h),
                           footprintHeap = Some(H()),
                           reinterpretWand = false)
          val rhs = magicWandSupporter.injectExhalingExp(eWand.right)
          val tv2 = tv.stepInto(c2, Description[ST, H, S]("Consume wand rhs"))
          consume(σ, σLhs.h, FullPerm(), rhs, pve, c2, tv2)((hLhs2, _, _, c3) => {
            val h2 = c3.reserveHeaps.head
            val c4 = c3.copy(reserveHeaps = c3.reserveHeaps.tail,
                             poldHeap = c1.poldHeap,
                             givenHeap = c1.givenHeap,
                             footprintHeap = c1.footprintHeap,
                             reinterpretWand = c1.reinterpretWand)
            /* ??? Producing the wand is not an option because we need to pass in σ.h */
            val ch = magicWandSupporter.createChunk(σ.γ, h, eWand)
            consume(σ, h2 + ch, FullPerm(), eIn, pve, c4, tv)((h3, _, _, c5) =>
              Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})

      case ast.Applying(eWand, eIn) =>
        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, eWand)

        val σWV = σ \+ Γ(wandValues)
        consume(σWV, h, FullPerm(), wand, pve, c.copy(reinterpretWand = false), tv)((h1, _, chs, c1) => {
          assert(chs.size == 1 && chs(0).isInstanceOf[MagicWandChunk[H]], "Unexpected list of consumed chunks: $chs")
          val ch = chs(0).asInstanceOf[MagicWandChunk[H]]
          /* TODO: See comment in exec/apply about givenHeap */
          val c1a = c1.copy(poldHeap = Some(ch.hPO),
                            givenHeap = Some(σ.h /* h ?*/),
                            reinterpretWand = c.reinterpretWand)
          consume(σWV, h1, FullPerm(), wand.left, pve, c1a, tv)((h2, _, _, c2) => {
            produce(σWV \ h2, decider.fresh, FullPerm(), wand.right, pve, c2, tv)((σ3, c3) => {
              val c3a = c3.copy(poldHeap = c1.poldHeap, givenHeap = c1.givenHeap)
              decider.prover.logComment(s"in consume/apply after producing RHS ${wand.right}}, before consuming $eIn")
              consume(σ, σ3.h, FullPerm(), eIn, pve, c3a, tv)((h4, _, _, c4) => {
                Q(h4, decider.fresh(sorts.Snap), Nil, c4)})})})})

      case ast.Folding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) =>

        val predicate = c.program.findPredicate(predicateName)
        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0a = c.incCycleCounter(predicate)
          evalp(σ, ePerm, pve, c0a, tv)((_tPerm, c1) => {
            if (decider.check(σ, IsPositive(_tPerm)))
              evals(σ, eArgs, pve, c1, tv)((tArgs, c2) => {
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                consume(σ \ insγ, h, FullPerm(), predicate.body, pve, c2, tv)((h1, snap, chs, c3) => { // TODO: What to do with the consumed chunks?
                  produce(σ \ h1, s => snap.convert(s), _tPerm, acc, pve, c3, tv)((σ2, c4) => {
                    val c4a = c4.decCycleCounter(predicate)
                    consume(σ2, σ2.h, FullPerm(), eIn, pve, c4a, tv)((h3, _, _, c5) => {
                      Q(h3, decider.fresh(sorts.Snap), Nil, c5)})})})})
            else
              Failure[ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), tv)})
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> folding next.P in e} is currently not " +
            "supported. It should be  possible to wrap 'folding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + φ)

      case ast.Exhaling(a) =>
        consume(σ \ h, h, FullPerm(), a, pve, c.copy(footprintHeap = Some(H())), tv)((h1, _, _, c1) =>
          Q(h1, decider.fresh(sorts.Snap), Nil, c1.copy(footprintHeap = c.footprintHeap)))

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expressions need to be evaluated in the initial heap(s) (σ.h, c.reserveEvalHeap) and
			 * not in the partially consumed heap(s) (h, c.reserveHeap).
			 */
      case _ =>
        def tryOrFail(σ: S) =
          decider.tryOrFail[(H, Term, List[DirectChunk], C)](σ)((σ1, QS, QF) =>
            eval(σ1, φ, pve, c, tv)((t, c1) =>
              decider.assert(σ1, t) {
                case true =>
                  assume(t)
                  QS((h, Unit, Nil, c1))
                case false =>
                  QF(Failure[ST, H, S, TV](pve dueTo AssertionFalse(φ), tv))
              })) _

        c.footprintHeap match {
          case Some(hFoot) =>
            val hCombined = σ.h + hFoot
//            var hNew = h
//            var cInner = c
            decider.inScope {
              tryOrFail(σ \ hCombined){case (hX, tX, dcsX, cX) =>
//                cInner = cX
                Success()}
            } && {
              Q(h /*hNew*/, Unit, Nil, c)
            }
          case None =>
            tryOrFail(σ)(Q.tupled)
        }
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
    if (c.footprintHeap.nonEmpty)
      return magicWandSupporter.consumeFromMultipleHeaps(σ, h :: c.reserveHeaps, id, pLoss, locacc, pve, c, tv)((hs, chs, c1/*, pcr*/) => {
        val c2 = c1.copy(reserveHeaps = hs.tail)
        val pcr = PermissionsConsumptionResult(false) // TODO: PermissionsConsumptionResult is bogus!
        val chunksFromReserveHeaps = chs.collect{case pair if pair._2 != 0 => pair._1}
        Q(hs.head, chs.head._1, c2.copy(footprintHeap = c2.footprintHeap.map(_ + H(chunksFromReserveHeaps))), pcr)})

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
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
