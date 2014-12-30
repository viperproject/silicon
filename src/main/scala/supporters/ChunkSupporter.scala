/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.ast
import silver.verifier.PartialVerificationError
import interfaces.{Evaluator, Consumer, Producer, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{Chunk, StateFactory, HeapCompressor, ChunkIdentifier, State, PathConditions, Heap, Store}
import state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk}
import state.terms._
import state.terms.perms.IsNoAccess
import silicon.utils

trait ChunkSupporter[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S]]
  { this:      Logging
          with Evaluator[ST, H, S, DefaultContext[H]]
          with Producer[ST, H, S, DefaultContext[H]]
          with Consumer[Chunk, ST, H, S, DefaultContext[H]]
          with Brancher[ST, H, S, DefaultContext[H]]
          with MagicWandSupporter[ST, H, PC, S]
          with HeuristicsSupporter[ST, H, PC, S] =>

  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]]

  object chunkSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

    private case class PermissionsConsumptionResult(consumedCompletely: Boolean)

    def consume(σ: S,
                h: H,
                id: ChunkIdentifier,
                tPerm: Term,
                pve: PartialVerificationError,
                c: C,
                locacc: ast.LocationAccess,
                optNode: Option[ast.Node with ast.Positioned] = None)
               (Q: (H, Term, List[CH], C) => VerificationResult)
               : VerificationResult = {

      val description = optNode.orElse(Some(locacc)).map(node => s"consume ${node.pos}: $node").get
//      val description = optNode match {
//        case Some(node) => s"consume ${node.pos}: $node"
//        case None => s"consume $id"
//      }

      heuristicsSupporter.tryOperation[H, Term, List[Chunk]](description)(σ, h, c)((σ1, h1, c1, QS) => {
        consume(σ, h1, id, tPerm, locacc, pve, c1)((h2, optCh, c2, results) =>
          optCh match {
            case Some(ch) =>
              val c3 = c2.snapshotRecorder match {
                case Some(sr) =>
                  c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(ch.id))))
//                  c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(ch.id))))
                case _ => c2}
              ch match {
                case fc: DirectFieldChunk =>
                  val snap = fc.value.convert(sorts.Snap)
                  QS(h2, snap, fc :: Nil, c3)
                case pc: DirectPredicateChunk =>
                  val h3 =
                    if (results.consumedCompletely)
                      pc.nested.foldLeft(h2){case (ha, nc) => ha - nc}
                    else
                      h2
                  QS(h3, pc.snap, pc :: Nil, c3)}
            case None =>
              /* Not having consumed anything could mean that we are in an infeasible
               * branch, or that the permission amount to consume was zero.
               */
              QS(h2, Unit, Nil, c2)
          })
      })(Q)
    }

    private def consume(σ: S,
                        h: H,
                        id: ChunkIdentifier,
                        pLoss: Term,
                        locacc: ast.LocationAccess,
                        pve: PartialVerificationError,
                        c: C)
                       (Q: (H, Option[DirectChunk], C, PermissionsConsumptionResult) => VerificationResult)
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

          val c3 =
            if (c2.recordEffects) {
              assert(chs.length == c2.consumedChunks.length)

              val consumedChunks3 =
                chs.zip(c2.consumedChunks).foldLeft(Stack[Seq[(Stack[Term], DirectChunk)]]()) {
                  case (accConsumedChunks, (optCh, consumed)) =>
                    optCh match {
                      case Some(ch) => ((guards -> ch) +: consumed) :: accConsumedChunks
                      case None => consumed :: accConsumedChunks
                    }
                }.reverse

              c2.copy(consumedChunks = consumedChunks3)
            } else
              c2
          //        val c3 = chs.last match {
          //          case Some(ch) if c2.recordEffects =>
          //            c2.copy(consumedChunks = c2.consumedChunks :+ (guards -> ch))
          //          case _ => c2
          //        }

          val usedChunks = chs.flatten
          /* Returning any of the usedChunks should be fine w.r.t to the snapshot
           * of the chunk, since consumeFromMultipleHeaps should have equated the
           * snapshots of all usedChunks.
           */
          Q(h + H(usedChunks), usedChunks.headOption, c3, pcr)})

      if (utils.consumeExactRead(pLoss, c)) {
        decider.withChunk[DirectChunk](σ, h, id, Some(pLoss), locacc, pve, c)(ch => {
          if (decider.check(σ, IsNoAccess(PermMinus(ch.perm, pLoss)))) {
            Q(h - ch, Some(ch), c, PermissionsConsumptionResult(true))}
          else
            Q(h - ch + (ch - pLoss), Some(ch), c, PermissionsConsumptionResult(false))})
      } else {
        decider.withChunk[DirectChunk](σ, h, id, None, locacc, pve, c)(ch => {
          decider.assume(PermLess(pLoss, ch.perm))
          Q(h - ch + (ch - pLoss), Some(ch), c, PermissionsConsumptionResult(false))})
      }
    }

    def produce(σ: S, h: H, ch: DirectChunk, c: C): (H, C) = {
      val (h1, matchedChunk) = heapCompressor.merge(σ, h, ch, c)
      val c1 = recordSnapshot(c, matchedChunk, ch)
      val c2 = recordProducedChunk(c1, ch, guards)

      (h1, c2)
    }

    private def recordSnapshot(c: C, matchedChunk: Option[DirectChunk], producedChunk: DirectChunk): C =
      c.snapshotRecorder match {
        case Some(sr) =>
          val sr1 = sr.addChunkToSnap(matchedChunk.getOrElse(producedChunk).id, guards, sr.currentSnap)
          c.copy(snapshotRecorder = Some(sr1))
        case _ => c
      }

    private def recordProducedChunk(c: C, producedChunk: DirectChunk, guards: Stack[Term]): C =
      c.recordEffects match {
        case true => c.copy(producedChunks = c.producedChunks :+ (guards -> producedChunk))
        case false => c
      }

  }
}
