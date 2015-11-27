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
import interfaces.state.{HeapCompressor, ChunkIdentifier, State, PathConditions, Heap, Store}
import state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk}
import state.terms._
import state.terms.perms.IsNoAccess
import silicon.utils

trait ChunkSupporter[ST <: Store[ST],
                     H <: Heap[H],
                     PC <: PathConditions[PC],
                     S <: State[ST, H, S]]
  { this:      Logging
          with Evaluator[ST, H, S, DefaultContext]
          with Producer[ST, H, S, DefaultContext]
          with Consumer[DirectChunk, ST, H, S, DefaultContext]
          with Brancher[ST, H, S, DefaultContext]  =>

  protected val decider: Decider[ST, H, PC, S, DefaultContext]
  protected val heapCompressor: HeapCompressor[ST, H, S, DefaultContext]
  protected val config: Config

  object chunkSupporter {
    private type C = DefaultContext
    private type CH = DirectChunk

    private case class PermissionsConsumptionResult(consumedCompletely: Boolean)

    def consume(σ: S,
                h: H,
                id: ChunkIdentifier,
                tPerm: Term,
                pve: PartialVerificationError,
                c: C,
                locacc: ast.LocationAccess,
                optNode: Option[ast.Node] = None)
               (Q: (H, Term, List[CH], C) => VerificationResult)
               : VerificationResult = {

      consume(σ, h, id, tPerm, locacc, pve, c)((h2, optCh, c2, results) =>
        optCh match {
          case Some(ch) =>
            ch match {
              case fc: DirectFieldChunk =>
                val snap = fc.value.convert(sorts.Snap)
                Q(h2, snap, fc :: Nil, c2)
              case pc: DirectPredicateChunk =>
                val h3 =
                  if (results.consumedCompletely)
                    pc.nested.foldLeft(h2){case (ha, nc) => ha - nc}
                  else
                    h2
                Q(h3, pc.snap, pc :: Nil, c2)}
          case None =>
            /* Not having consumed anything could mean that we are in an infeasible
             * branch, or that the permission amount to consume was zero.
             */
            Q(h2, Unit, Nil, c2)
        })
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

      if (silicon.utils.consumeExactRead(pLoss, c)) {
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

      (h1, c1)
    }
  }
}
