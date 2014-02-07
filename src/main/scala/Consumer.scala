package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.{MagicWandChunkOutdated, InsufficientPermission, NonPositivePermission, AssertionFalse, MagicWandChunkNotFound}
import sil.ast.utility.Permissions.isConditional
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, ChunkIdentifier}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.reporting.TraceView
import interfaces.decider.Decider
import state.{SymbolConvert, DirectChunk, DirectFieldChunk, DirectPredicateChunk, MagicWandChunk}
import state.terms._
import reporting.{DefaultContext, Consuming, ImplBranching, IfBranching, Bookkeeper}
import supporters.MagicWandSupporter

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

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.assume


	protected val chunkFinder: ChunkFinder[P, ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(Ïƒ: S, p: P, Ï†: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult = {

    /* TODO: What should the result of current-perms(x.f) be when it occurs on the rhs of a magic wand? */

    val c0 = c.copy(reserveEvalHeap = c.reserveHeap)

    consume2(Ïƒ, Ïƒ.h, p, Ï†, pve, c0, tv)((h1, t, dcs, c1) =>
      Q(Ïƒ \ h1, t, dcs, c1))
  }

  def consumes(Ïƒ: S,
               p: P,
               Ï†s: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes2(Ïƒ, Ïƒ.h, p, Ï†s, Nil, Nil, pvef, c, tv)(Q)

  private def consumes2(Ïƒ: S, h: H, p: P, Ï†s: Seq[ast.Expression], ts: List[Term], dcs: List[DirectChunk], pvef: ast.Expression => PartialVerificationError, c: C, tv: TV)
                       (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    if (Ï†s.isEmpty)
      Q(Ïƒ \ h, ts.reverse, dcs.reverse, c)
    else
      consume(Ïƒ, h, p, Ï†s.head, pvef(Ï†s.head), c, tv)((h1, t, dcs1, c1) =>
        consumes2(Ïƒ, h1, p, Ï†s.tail, t :: ts, dcs1 ::: dcs, pvef, c1, tv)(Q))

	protected def consume(Ïƒ: S, h: H, p: P, Ï†: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                 (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

		consume2(Ïƒ, h, p, Ï†, pve, c, tv)(Q)

  protected def consume2(Ïƒ: S, h: H, p: P, Ï†: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                  (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                        : VerificationResult = {

    val tv1 = tv.stepInto(c, Consuming[ST, H, S](Ïƒ, h, p, Ï†))

    internalConsume(Ïƒ, h, p, Ï†, pve, c, tv1)((h1, s1, dcs, c1) => {
      tv1.currentStep.ÏƒPost = Ïƒ \ h1
      Q(h1, s1, dcs, c1)
    })
  }

	private def internalConsume(Ïƒ: S, h: H, p: P, Ï†: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                  (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                        : VerificationResult = {

    logger.debug(s"\CONSUME ${Ï†.pos}: ${Ï†}")
    logger.debug(stateFormatter.format(Ïƒ))
    if (c.reserveHeap.nonEmpty)
      logger.debug("hR = " + stateFormatter.format(c.reserveHeap.get))
		logger.debug("h = " + stateFormatter.format(h))

		val consumed = Ï† match {
      case ast.InhaleExhaleExp(_, a1) =>
        consume(Ïƒ, h, p, a1, pve, c, tv)(Q)

      case ast.And(a1, a2) if !Ï†.isPure =>
				consume(Ïƒ, h, p, a1, pve, c, tv)((h1, s1, dcs1, c1) =>
					consume(Ïƒ, h1, p, a2, pve, c1, tv)((h2, s2, dcs2, c2) =>
						Q(h2, Combine(s1.convert(sorts.Snap), s2.convert(sorts.Snap)), dcs1 ::: dcs2, c2)))

      case ast.Implies(e0, a0) if !Ï†.isPure =>
				eval(Ïƒ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => consume(Ïƒ, h, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !Ï†.isPure =>
        eval(Ïƒ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => consume(Ïƒ, h, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => consume(Ïƒ, h, p, a2, pve, c2, tv1)(Q)))

      /* Field and predicate access predicates */
      case ast.AccessPredicate(locacc, perm) =>
        withChunkIdentifier(Ïƒ, locacc, true, pve, c, tv)((id, c1) =>
              evalp(Ïƒ, perm, pve, c1, tv)((tPerm, c2) =>
                if (decider.isPositive(tPerm, !isConditional(perm)))
                  consumePermissions(Ïƒ, h, id, p * tPerm, locacc, pve, c2, tv)((h1, ch, c3, results) =>
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

                      case _ => sys.error(s"Unexpected chunk after consuming $Ï†: $ch")})
                else
                  Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(perm), c2, tv)))

      /* TODO: Needs to consider both heaps. Try to merge this code with consumeIncludingReserveHeap. */
      case _ if Ï†.typ == ast.types.Wand =>
        /* Resolve wand and get mapping from (possibly renamed) local variables to their values. */
        val (wand, wandValues) = magicWandSupporter.resolveWand(Ïƒ, Ï†)
        val Ïƒ0 = Ïƒ \+ Î“(wandValues)

        /* If necessary, reinterprets the wand chunk. */
        def reinterpret(ch: MagicWandChunk[H], c: C, tv: TV)
               (Q: C => VerificationResult)
               : VerificationResult = {

          if (!c.reinterpretWand)
            Q(c)
          else {
            /* Collect pold-expressions together with conditional guards they are nested in.
             * For example, b ==> pold(e) will be returned as (b, pold(e)).
             */
            val pathConditionedPOlds = magicWandSupporter.pathConditionedPOlds(wand)
            /* Extract e from pold(e) and turn the list of pairs (b, pold(e)) into a list
             * of terms of the shape b && e == pold(e).
             */
            val eqs = pathConditionedPOlds.map{case (pc, po) =>
              val eq = ast.Equals(po.exp, po)(po.pos, po.info)
              ast.And(pc, eq)(eq.pos, eq.info)
            }
            val eSame = ast.utils.BigAnd(eqs)
            /* Check the generated equalities. */
            eval(Ïƒ0, eSame, pve, c.copy(poldHeap = Some(ch.hPO)), tv)((tSame, c1) =>
              if (decider.assert(tSame))
                Q(c1.copy(poldHeap = c.poldHeap))
              else
                Failure[C, ST, H, S, TV](pve dueTo MagicWandChunkOutdated(wand), c1, tv))}}

        /* TODO: Getting id by first creating a chunk is not elegant. */
        val id = magicWandSupporter.createChunk(Ïƒ0.Î³, Ïƒ0.h, wand).id
        decider.getChunk[MagicWandChunk[H]](h, id) match {
          case Some(ch) =>
            reinterpret(ch, c, tv)(c2 =>
              Q(h - ch, decider.fresh(sorts.Snap), List(ch), c2))
          case None if c.reserveHeap.nonEmpty =>
            decider.getChunk[MagicWandChunk[H]](c.reserveHeap.get, id) match {
              case Some(ch) =>
                reinterpret(ch, c, tv)(c2 => {
                  val c3 = c2.copy(reserveHeap = Some(c.reserveHeap.get - ch))
                  Q(h, decider.fresh(sorts.Snap), List(ch), c3)})
              case None =>
                Failure[C, ST, H, S, TV](pve dueTo MagicWandChunkNotFound(wand), c, tv)}
          case None =>
            Failure[C, ST, H, S, TV](pve dueTo MagicWandChunkNotFound(wand), c, tv)}

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expressions need to be evaluated in the initial heap(s) (Ïƒ.h, c.reserveEvalHeap) and
			 * not in the partially consumed heap(s) (h, c.reserveHeap).
			 */
      case _ =>
        eval(Ïƒ, Ï†, pve, c, tv)((t, c1) =>
          if (decider.assert(t)) {
            assume(t)
            Q(h, Unit, Nil, c1)
          } else
            Failure[C, ST, H, S, TV](pve dueTo AssertionFalse(Ï†), c1, tv))
		}

		consumed
	}

  private def consumePermissions(Ïƒ: S,
                                 h: H,
                                 id: ChunkIdentifier,
                                 pLoss: P,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q: (H, DirectChunk, C, PermissionsConsumptionResult) => VerificationResult)
                                : VerificationResult = {

    // TODO: Integrate into regular (non-)exact consumption!
    if (c.reserveHeap.nonEmpty)
      return consumeIncludingReserveHeap(Ïƒ, h, id, pLoss, locacc, pve, c, tv)(Q)

    if (consumeExactRead(pLoss, c)) {
      withChunk[DirectChunk](h, id, pLoss, locacc, pve, c, tv)(ch => {
        if (decider.assertNoAccess(ch.perm - pLoss)) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      withChunk[DirectChunk](h, id, locacc, pve, c, tv)(ch => {
        assume(pLoss < ch.perm)
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }

  private def consumeIncludingReserveHeap(Ïƒ: S,
                                          h: H,
                                          id: ChunkIdentifier,
                                          pLoss: P,
                                          locacc: ast.LocationAccess,
                                          pve: PartialVerificationError,
                                          c: C,
                                          tv: TV)
                                         (Q: (H, DirectChunk, C, PermissionsConsumptionResult) => VerificationResult)
                                         : VerificationResult = {

    val (h1, optCh1, pLoss1, c1) = consumeMaxPermissions(h, id, pLoss, c, tv)

    if (decider.assertNoAccess(pLoss1)) {
      Q(h1, optCh1.get, c1, PermissionsConsumptionResult(false)) // TODO: PermissionsConsumptionResult is bogus!
    } else {
      val (h2, optCh2, pLoss2, c2) = consumeMaxPermissions(c1.reserveHeap.get, id, pLoss1, c1, tv)
      if (decider.assertNoAccess(pLoss2)) {
        val tVal = (optCh1, optCh2) match {
          case (Some(fc1: DirectFieldChunk), Some(fc2: DirectFieldChunk)) => fc1.value === fc2.value
          case (Some(pc1: DirectPredicateChunk), Some(pc2: DirectPredicateChunk)) => pc1.snap === pc2.snap
          case _ => True()}
        assume(tVal)
        val c3 = c2.copy(reserveHeap = Some(h2))
        Q(h1, optCh2.get, c3, PermissionsConsumptionResult(false)) // TODO: PermissionsConsumptionResult is bogus!
      } else {
        Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c2, tv)
      }
    }
  }

  private def consumeMaxPermissions(h: H,
                                    id: ChunkIdentifier,
                                    pLoss: P,
                                    c: C,
                                    tv: TV)
                                   : (H, Option[DirectChunk], P, C) = {

    decider.getChunk[DirectChunk](h, id) match {
      case result @ Some(ch) =>
        val (pToConsume, pKeep) =
          if (decider.isAsPermissive(ch.perm, pLoss)) (NoPerm(), ch.perm - pLoss)
          else (pLoss - ch.perm, NoPerm())
        val h1 =
          if (decider.assertNoAccess(pKeep)) h - ch
          else h - ch + (ch \ pKeep)
        (h1, result, pToConsume, c)

      case None => (h, None, pLoss, c)
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
