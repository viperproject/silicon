/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import interfaces.{Evaluator, Consumer, Producer, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{StateFactory, Chunk, State, PathConditions, Heap, Store}
import viper.silicon.state.{PredicateChunkIdentifier, NestedPredicateChunk, NestedFieldChunk, DefaultContext,
    DirectPredicateChunk, DirectFieldChunk, MagicWandChunk}
import state.terms._

trait PredicateSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[Chunk, ST, H, S, DefaultContext[H]]
            with ChunkSupporter[ST, H, PC, S] =>

  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  object predicateSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

    def fold(σ: S, predicate: ast.Predicate, tArgs: List[Term], tPerm: Term, pve: PartialVerificationError, c: C)
            (Q: (S, C) => VerificationResult)
            : VerificationResult = {

      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      consume(σ \ insγ, tPerm, predicate.body, pve, c)((σ1, snap, dcs, c1) => {
        val ncs = dcs flatMap {
          case fc: DirectFieldChunk => Some(new NestedFieldChunk(fc))
          case pc: DirectPredicateChunk => Some(new NestedPredicateChunk(pc))
          case _: MagicWandChunk => None}
        val id = PredicateChunkIdentifier(predicate.name, tArgs)
        /* TODO: Chunk should be produced (or added via ChunkSupporter)! */
        val (h, t, tPerm1) = decider.getChunk[DirectPredicateChunk](σ, σ1.h, id, c1) match {
          case Some(pc) =>
            (σ1.h - pc,
             pc.snap.convert(sorts.Snap) === snap.convert(sorts.Snap),
             PermPlus(pc.perm, tPerm))
          case None =>
            (σ1.h, True(), tPerm)}
        decider.assume(t)
        val h1 = h + DirectPredicateChunk(predicate.name, tArgs, snap, tPerm1, ncs) + H(ncs)
        Q(σ \ h1, c1)})
    }

    def unfold(σ: S,
               predicate: ast.Predicate,
               tArgs: List[Term],
               tPerm: Term,
               pve: PartialVerificationError,
               c: C,
               locacc: ast.LocationAccess)
              (Q: (S, C) => VerificationResult)
              : VerificationResult = {

      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      val id = PredicateChunkIdentifier(predicate.name, tArgs)
      chunkSupporter.consume(σ, σ.h, id, tPerm, pve, c, locacc)((h1, snap, _, c1) =>
        produce(σ \ h1 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c1)((σ2, c2) =>
          Q(σ2 \ σ.γ, c2)))
    }
  }
}
