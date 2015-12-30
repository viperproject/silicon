/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import org.slf4s.Logging
import silver.ast
import silver.verifier.PartialVerificationError
import interfaces.{Evaluator, Consumer, Producer, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{Chunk, StateFactory, HeapCompressor, ChunkIdentifier, State, PathConditions, Heap, Store}
import state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk, QuantifiedChunk}
import state.terms._
import state.terms.perms.IsNoAccess

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
  protected val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val config: Config

  import stateFactory._

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
               (Q: (H, Term, C) => VerificationResult)
               : VerificationResult = {

      val description = optNode.orElse(Some(locacc)).map(node => s"consume ${node.pos}: $node").get
//      val description = optNode match {
//        case Some(node) => s"consume ${node.pos}: $node"
//        case None => s"consume $id"
//      }

      heuristicsSupporter.tryOperation[H, Term](description)(σ, h, c)((σ1, h1, c1, QS) => {
        consume(σ, h1, id, tPerm, locacc, pve, c1)((h2, optCh, c2, results) =>
          optCh match {
            case Some(ch) =>
              QS(h2, ch.snap.convert(sorts.Snap), c2)
            case None =>
              /* Not having consumed anything could mean that we are in an infeasible
               * branch, or that the permission amount to consume was zero.
               */
            QS(h2, Unit, c2)
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
                      case Some(ch) => ((c2.branchConditions -> ch) +: consumed) :: accConsumedChunks
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

      if (state.terms.utils.consumeExactRead(pLoss, c.constrainableARPs)) {
        decider.withChunk[DirectChunk](σ, h, id, Some(pLoss), locacc, pve, c)((ch, c1) => {
          if (decider.check(σ, IsNoAccess(PermMinus(ch.perm, pLoss)), config.checkTimeout())) {
            Q(h - ch, Some(ch), c1, PermissionsConsumptionResult(true))}
          else
            Q(h - ch + (ch - pLoss), Some(ch), c1, PermissionsConsumptionResult(false))})
      } else {
        decider.withChunk[DirectChunk](σ, h, id, None, locacc, pve, c)((ch, c1) => {
          decider.assume(PermLess(pLoss, ch.perm))
          Q(h - ch + (ch - pLoss), Some(ch), c1, PermissionsConsumptionResult(false))})
      }
    }

    def produce(σ: S, h: H, ch: DirectChunk, c: C): (H, C) = {
      val (h1, matchedChunk) = heapCompressor.merge(σ, h, ch, c)
      val c1 = c//recordSnapshot(c, matchedChunk, ch)
      val c2 = recordProducedChunk(c1, ch, c.branchConditions)

      (h1, c2)
    }

    private def recordProducedChunk(c: C, producedChunk: DirectChunk, guards: Stack[Term]): C =
      c.recordEffects match {
        case true => c.copy(producedChunks = c.producedChunks :+ (guards -> producedChunk))
        case false => c
      }

  }
}
