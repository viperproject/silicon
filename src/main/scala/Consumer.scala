/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.{VerificationError, PartialVerificationError}
import silver.verifier.reasons.{NamedMagicWandChunkNotFound, NegativePermission, AssertionFalse, MagicWandChunkNotFound}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, StateFactory, StateFormatter, ChunkIdentifier}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.state.factoryUtils.Ø
import reporting.Bookkeeper
import state.{DefaultContext, DirectChunk, DirectFieldChunk, DirectPredicateChunk, MagicWandChunk,
    MagicWandChunkIdentifier}
import state.terms._
import state.terms.perms.IsNoAccess
import supporters.{HeuristicsSupporter, MagicWandSupporter}

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S]]
		extends Consumer[Chunk, ST, H, S, DefaultContext[H]]
		{ this: Logging with Evaluator[ST, H, S, DefaultContext[H]]
									  with Brancher[ST, H, S, DefaultContext[H]]
                    with Producer[ST, H, S, DefaultContext[H]]
                    with MagicWandSupporter[ST, H, PC, S]
                    with HeuristicsSupporter[ST, H, PC, S]
                    with LetHandler[ST, H, S, DefaultContext[H]] =>

  private type C = DefaultContext[H]
  private type CH = Chunk

  protected implicit val manifestH: Manifest[H]

	protected val decider: Decider[ST, H, PC, S, C]
  import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val bookkeeper: Bookkeeper
  protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: Term, φ: ast.Expression, pve: PartialVerificationError, c: C)
             (Q: (S, Term, List[CH], C) => VerificationResult)
             : VerificationResult = {

    consume(σ, σ.h, p, φ.whenExhaling, pve, c)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))
  }

  def consumes(σ: S,
               p: Term,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[CH], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), pvef, c)(Q)

  private def consumes(σ: S,
                       h: H,
                       p: Term,
                       φs: Seq[ast.Expression],
                       pvef: ast.Expression => PartialVerificationError,
                       c: C)
                       (Q: (S, Term, List[CH], C) => VerificationResult)
                       : VerificationResult =

    /* TODO: See the code comment about produce vs. produces in DefaultProducer.produces.
     *       The same applies to consume vs. consumes.
     */

    if (φs.isEmpty)
      Q(σ \ h, Unit, Nil, c)
    else {
      val φ = φs.head

      if (φ.tail.isEmpty)
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          Q(σ \ h1, s1, dcs1, c1))
      else
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          consumes(σ, h1, p, φs.tail, pvef, c1)((h2, s2, dcs2, c2) => {
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)
          }))
    }

  protected def consume(σ: S, h: H, p: Term, φ: ast.Expression, pve: PartialVerificationError, c: C)
                       (Q: (H, Term, List[CH], C) => VerificationResult)
                       : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
      if (c.reserveHeaps.nonEmpty)
        logger.debug("hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
    }

		val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1)((h2, s2, dcs2, c2) => {
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

						Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)}))

      case ast.Implies(e0, a0) if !φ.isPure =>
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
				eval(σC, e0, pve, c)((t0, c1) =>
					branch(σC, t0, c1,
						(c2: C) => consume(σ, h, p, a0, pve, c2)(Q),
						(c2: C) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
        eval(σC, e0, pve, c)((t0, c1) =>
          branch(σC, t0, c1,
            (c2: C) => consume(σ, h, p, a1, pve, c2)(Q),
            (c2: C) => consume(σ, h, p, a2, pve, c2)(Q)))

      case let: ast.Let if !let.isPure =>
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
        handle[ast.Expression](σC, let, pve, c)((γ1, body, c1) =>
          consume(σ \+ γ1, h, p, body, pve, c1)(Q))

      case ast.AccessPredicate(locacc, perm) =>
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
        withChunkIdentifier(σC, locacc, true, pve, c)((id, c1) =>
          eval(σC, perm, pve, c1)((tPerm, c2) =>
            decider.assert(σC, perms.IsNonNegative(tPerm)){
              case true =>
                heuristicsSupporter.tryOperation[H, Term, List[Chunk]](s"consumePermissions ${φ.pos}: $φ")(σC, h, c2)((σC, h, c2, QS) => {
                  consumePermissions(σC, h, id, PermTimes(p, tPerm), locacc, pve, c2)((h1, ch, c3, results) => {
                    val c4 = c3.snapshotRecorder match {
                      case Some(sr) =>
                        c3.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(ch.id))))
                      case _ => c3}
                    ch match {
                      case fc: DirectFieldChunk =>
                        val snap = fc.value.convert(sorts.Snap)
                        QS(h1, snap, fc :: Nil, c4)
                      case pc: DirectPredicateChunk =>
                        val h2 =
                          if (results.consumedCompletely)
                            pc.nested.foldLeft(h1){case (ha, nc) => ha - nc}
                          else
                            h1
                        QS(h2, pc.snap, pc :: Nil, c4)}})
                })(Q)

              case false =>
                Failure[ST, H, S](pve dueTo NegativePermission(perm))}))

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(φ))

      /* Handle wands or wand-typed variables */
      case _ if φ.typ == ast.types.Wand && magicWandSupporter.isDirectWand(φ) =>
        def QL(σ: S, h: H, id: MagicWandChunkIdentifier, wand: ast.MagicWand, ve: VerificationError, c: C) = {
          heuristicsSupporter.tryOperation[H, Term, List[Chunk]](s"consume wand $wand")(σ, h, c)((σ, h, c, QS) => {
            val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
            val hs =
              if (c.exhaleExt) c.reserveHeaps
              else Stack(h)

            magicWandSupporter.doWithMultipleHeaps(hs, c)((h1, c1) =>
              decider.getChunk[MagicWandChunk](σC, h1, id, c1) match {
                case someChunk @ Some(ch) => (someChunk, h1 - ch, c1)
                case _ => (None, h1, c1)
              }
            ){case (Some(ch), hs1, c1) =>
                assert(c1.exhaleExt == c.exhaleExt)
                if (c.exhaleExt) {
                  /* transfer: move ch into h = σUsed*/
                  assert(hs1.size == c.reserveHeaps.size)
                  QS(h + ch, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs1))
                } else {
                  assert(hs1.size == 1)
                  assert(c.reserveHeaps == c1.reserveHeaps)
                  QS(hs1.head, decider.fresh(sorts.Snap), List(ch), c1)
                }

              case _ => Failure[ST, H, S](ve)}
          })(Q)
        }

        φ match {
          case wand: ast.MagicWand =>
            magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) => {
              val ve = pve dueTo MagicWandChunkNotFound(wand)
              QL(σ, h, chWand.id, wand, ve, c1)})
          case v: ast.LocalVariable =>
            val tWandChunk = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
            val ve = pve dueTo NamedMagicWandChunkNotFound(v)
            QL(σ, h, tWandChunk.id, tWandChunk.ghostFreeWand, ve, c)
          case _ => sys.error(s"Expected a magic wand, but found node $φ")
        }

      case pckg @ ast.Packaging(eWand, eIn) =>
//        val pve = PackagingFailed(pckg)
        magicWandSupporter.packageWand(σ, eWand, pve, c)((chWand, c1) => {
          val h2 = h + chWand /* h2 = σUsed'' */
          val topReserveHeap = c1.reserveHeaps.head + h2
          val c2 = c1.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.drop(2),
                           exhaleExt = c.exhaleExt,
                           lhsHeap = None)
          val σEmp = Σ(σ.γ, Ø, σ.g)
          consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c2)((h3, _, _, c3) =>
            Q(h3, decider.fresh(sorts.Snap), Nil, c3))})

      case ast.Applying(eWandOrVar, eIn) =>
        val (eWand, eLHSAndWand, γ1) = eWandOrVar match {
          case _eWand: ast.MagicWand =>
            (_eWand, ast.And(_eWand.left, _eWand)(_eWand.left.pos, _eWand.left.info), σ.γ)
          case v: ast.LocalVariable =>
            val chWand = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
            val _eWand = chWand.ghostFreeWand
            (_eWand, ast.And(_eWand.left, _eWand)(v.pos, v.info), Γ(chWand.bindings))
              /* Note that wand reference v is most likely not bound in tChunk.bindings.
               * Since wands cannot be recursive, this shouldn't be a problem,
               * as long as v doesn't need to be looked during
               * magicWandSupporter.applyingWand (for whatever reason).
               */
          case _ => sys.error(s"Expected a magic wand, but found node $φ")
        }

        heuristicsSupporter.tryOperation[S, H](s"applying $eWand")(σ, h, c)((σ, h, c, QS) =>
          magicWandSupporter.applyingWand(σ, γ1, eWand, eLHSAndWand, pve, c)(QS)){case (σ1, h1, c1) =>
            consume(σ1, h1, FullPerm(), eIn, pve, c1)((h4, _, _, c4) =>
              Q(h4, decider.fresh(sorts.Snap), Nil, c4))}

      case ast.Folding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) =>

        heuristicsSupporter.tryOperation[S, H](s"folding $acc")(σ, h, c)((σ, h, c, QS) =>
          magicWandSupporter.foldingPredicate(σ, acc, pve, c)(QS)){case (σ1, h1, c1) =>
            consume(σ1, h1, FullPerm(), eIn, pve, c1)((h4, _, _, c4) =>
              Q(h4, decider.fresh(sorts.Snap), Nil, c4))}

      case ast.Unfolding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) if c.exhaleExt && !φ.isPure =>

        heuristicsSupporter.tryOperation[S, H](s"unfolding $acc")(σ, h, c)((σ, h, c, QS) =>
          magicWandSupporter.unfoldingPredicate(σ, acc, pve, c)(QS)){case (σ1, h1, c1) =>
            consume(σ1, h1, FullPerm(), eIn, pve, c1)((h4, _, _, c4) =>
              Q(h4, decider.fresh(sorts.Snap), Nil, c4))}

			/* Any regular Expressions, i.e. boolean and arithmetic */
      case _ =>
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, h, c)
        val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
        decider.tryOrFail[(H, Term, List[CH], C)](σC, c0)((σC1, QS, QF) => {
          eval(σC1, φ, pve, c0)((t, c1) =>
            decider.assert(σC1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c1.copy(reserveHeaps = c.reserveHeaps, exhaleExt = c.exhaleExt)))
              case false =>
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(φ)))
            })
        })(Q.tupled)
		}

		consumed
	}

  private def consumePermissions(σ: S,
                                 h: H,
                                 id: ChunkIdentifier,
                                 pLoss: Term,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C)
                                (Q: (H, DirectChunk, C, PermissionsConsumptionResult) => VerificationResult)
                                : VerificationResult = {

    /* TODO: Integrate into regular, (non-)exact consumption that follows afterwards */
    if (c.exhaleExt)
      /* Function "transfer" from wands paper.
       * Permissions are transferred from the stack of heaps to σUsed, which is
       * h in the current context.
       */
      return magicWandSupporter.consumeFromMultipleHeaps(σ, c.reserveHeaps, id, pLoss, locacc, pve, c)((hs, chs, c1/*, pcr*/) => {
        val c2 = c1.copy(reserveHeaps = hs)
        val pcr = PermissionsConsumptionResult(false) // TODO: PermissionsConsumptionResult is bogus!

        /* The last heap in the stack should be the one corresponding to the
         * pre-package heap. It should be sufficient to record consumptions
         * from this heap in order to be able to join branches after executing
         * a package-statement.
         */
        val c3 = chs.last match {
          case Some(ch) if c2.recordConsumedChunks =>
            c2.copy(consumedChunks = c2.consumedChunks :+ (guards -> ch))
          case _ => c2
        }

        val usedChunks = chs.flatten
        /* Returning any of the usedChunks should be fine w.r.t to the snapshot
         * of the chunk, since consumeFromMultipleHeaps should have equated the
         * snapshots of all usedChunks.
         */
        Q(h + H(usedChunks), usedChunks.head, c3, pcr)})

    if (utils.consumeExactRead(pLoss, c)) {
      decider.withChunk[DirectChunk](σ, h, id, Some(pLoss), locacc, pve, c)(ch => {
        if (decider.check(σ, IsNoAccess(PermMinus(ch.perm, pLoss)))) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      decider.withChunk[DirectChunk](σ, h, id, None, locacc, pve, c)(ch => {
        assume(PermLess(pLoss, ch.perm))
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
