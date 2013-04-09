package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.{NegativeFraction, ReceiverNull, AssertionFalse}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, StateFactory, Chunk}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.reporting.TraceView
import interfaces.decider.Decider
import state.{TypeConverter, DirectChunk, DirectFieldChunk, DirectPredicateChunk}
import state.terms._
import reporting.{DefaultContext, Consuming, ImplBranching, IfBranching, Bookkeeper}

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
									  with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshARP

  protected val typeConverter: TypeConverter
  import typeConverter.toSort

	protected val chunkFinder: ChunkFinder[P, ST, H, S, C, TV]
	import chunkFinder.withChunk

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult =

    consume2(σ, σ.h, p, φ, pve, c, tv)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))

  /**
   *
   * @param σ
   * @param p
   * @param φs
   * @param pvef
   * @param c
   * @param tv
   * @param Q
   * @return
   */
  def consumes(σ: S,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes2(σ, σ.h, p, φs, Nil, Nil, pvef, c, tv)(Q)

  private def consumes2(σ: S, h: H, p: P, φs: Seq[ast.Expression], ts: List[Term], dcs: List[DirectChunk], pvef: ast.Expression => PartialVerificationError, c: C, tv: TV)
                       (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    if (φs.isEmpty)
      Q(σ, ts.reverse, dcs.reverse, c)
    else
      consume(σ, h, p, φs.head, pvef(φs.head), c, tv)((h1, t, dcs1, c1) =>
        consumes2(σ, h1, p, φs.tail, t :: ts, dcs1 ::: dcs, pvef, c1, tv)(Q))

	protected def consume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                 (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

		consume2(σ, h, p, φ, pve, c, tv)(Q)

  protected def consume2(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
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

		logger.debug("\nCONSUME " + φ.toString)
		logger.debug(stateFormatter.format(σ))
		logger.debug("h = " + stateFormatter.format(h))

		val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c, tv)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1, tv)((h2, s2, dcs2, c2) =>
						Q(h2, Combine(s1.convert(sorts.Snap), s2.convert(sorts.Snap)), dcs1 ::: dcs2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => consume(σ, h, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => consume(σ, h, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => consume(σ, h, p, a2, pve, c2, tv1)(Q)))

      /* Access to fields or predicates */
      case ast.AccessPredicate(memloc @ ast.MemoryLocation(eRcvr, id), perm) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          if (decider.assert(tRcvr !== Null()))
            evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
              if (decider.isNonNegativeFraction(tPerm))
                consumePermissions(σ, h, p * tPerm, memloc, tRcvr, pve, c2, tv)((h1, ch, c3, results) =>
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
                      Q(h2, pc.snap, pc :: Nil, c3)})
              else
                Failure[C, ST, H, S, TV](pve dueTo NegativeFraction(perm), c2, tv))
          else
            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))

//      case qe @ ast.Quantified(
//                  ast.Exists(),
//                  qvar,
//                  ast.BinaryOp(
//                    _: ast.And,
//                    rdStarConstraints,
//                    pe @ ast.FieldAccessPredicate(ast.FieldLocation(rcvr, field), _)))
//           if toSort(qvar.dataType) == sorts.Perms =>
//
//        eval(σ, rcvr, pve, c, tv)((tRcvr, c1) =>
//          if (decider.assert(tRcvr !== Null()))
//            withChunk[DirectFieldChunk](h, tRcvr, field.name, rcvr, pve, c1, tv)(fc => {
//              val witness = qvar
//              val (tWitness, _) = freshPermVar(witness.name)
//              val σ1 = σ \+ (witness, tWitness)
//              eval(σ1, rdStarConstraints, pve, c1, tv)((tRdStarConstraints, c2) => {
//                val pWitness = PermissionsTuple(StarPerms(tWitness))
//                val tConstraints = And(tRdStarConstraints, fc.perm > pWitness)
//                assume(tConstraints, c2)
//                Q(h - fc + (fc - pWitness), fc.value.convert(sorts.Snap), fc :: Nil, c2)})})
//          else
//            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(rcvr), c1, tv))

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
			 * not in the partially consumed heap (h).
			 */
      case _ =>
        // assert(σ, h, φ, m, ExpressionMightEvaluateToFalse, Q)
        eval(σ, φ, pve, c, tv)((t, c) =>
          if (decider.assert(t)) {
            assume(t, c)
            Q(h, Unit, Nil, c)
          } else
            Failure[C, ST, H, S, TV](pve dueTo AssertionFalse(φ), c, tv))
		}

		consumed
	}

  private def consumePermissions(σ: S,
                                 h: H,
                                 pLoss: P,
                                 memloc: ast.MemoryLocation,
                                 tRcvr: Term,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q:     (H, DirectChunk, C, PermissionsConsumptionResult)
                                     => VerificationResult)
                                :VerificationResult = {

    val eRcvr = memloc.rcv
    val id = memloc.loc.name

    if (consumeExactRead(pLoss, c)) {
      withChunk[DirectChunk](h, tRcvr, id, pLoss, eRcvr, pve, c, tv)(ch => {
        if (decider.assertNoAccess(ch.perm - pLoss)) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      withChunk[DirectChunk](h, tRcvr, id, eRcvr, pve, c, tv)(ch => {
        assume(pLoss < ch.perm, c)
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }

  private def consumeExactRead(fp: P, c: C): Boolean = fp match {
//    case _: ReadPerm if !c.consumeExactReads => false
    case TermPerm(v: Var) => !c.constrainableARPs.contains(v)
    case TermPerm(t) => sys.error(s"[consumeExactRead] Found unexpected case $fp")
    case _: WildcardPerm => false
    case PermPlus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermMinus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermTimes(t0, t1) => consumeExactRead(t0, c) && consumeExactRead(t1, c)
    case IntPermTimes(_, t1) => consumeExactRead(t1, c)
//    case _ => true
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
