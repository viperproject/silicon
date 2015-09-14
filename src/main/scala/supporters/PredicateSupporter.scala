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

      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */

      /* [2014-12-13 Malte] Changing the store doesn't interact well with the
       * snapshot recorder, see the comment in PredicateSupporter.unfold.
       * However, since folding cannot (yet) be used inside functions, we can
       * still overwrite the binding of local variables in the store.
       * An alternative would be to introduce fresh local variables, and to
       * inject them into the predicate body. See commented code below.
       */
      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      consume(σ \ insγ, tPerm, body, pve, c)((σ1, snap, dcs, c1) => {
        val ncs = dcs flatMap {
          case fc: DirectFieldChunk => Some(new NestedFieldChunk(fc))
          case pc: DirectPredicateChunk => Some(new NestedPredicateChunk(pc))
          case _: MagicWandChunk => None}
        val ch = DirectPredicateChunk(predicate.name, tArgs, snap, tPerm, ncs)
        val (h1, c2) = chunkSupporter.produce(σ1, σ1.h, ch, c1)
        val h2 = h1 + H(ncs)
        Q(σ \ h2, c2)})
    }

    def unfold(σ: S,
               predicate: ast.Predicate,
               tArgs: List[Term],
               tPerm: Term,
               pve: PartialVerificationError,
               c: C,
               pa: ast.PredicateAccess /* TODO: Make optional (as in magicWandSupporter.foldingPredicate) */)
              (Q: (S, C) => VerificationResult)
              : VerificationResult = {

      /* [2014-12-10 Malte] Changing the store (insγ) doesn't play nicely with the
       * snapshot recorder because it might result in the same local variable
       * being bound to different terms, e.g., in the case of fun3 at the end of
       * functions/unfolding.sil, where the formal predicate argument x is bound
       * to y and y.n.
       */

//      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      val id = PredicateChunkIdentifier(predicate.name, tArgs)
      chunkSupporter.consume(σ, σ.h, id, tPerm, pve, c, pa)((h1, snap, chs, c1) => {
        /* [2014-12-10 Malte] The snapshot recorder used to be updated in
         * DefaultConsumer:Unfolding, but it seems that the old value of currentSnap
         * always corresponds to the new value. I am not sure why, though.
         */
//        val c1a = c1.snapshotRecorder match {
//          case Some(sr) =>
//            c1.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(chs(0).id))))
//          case _ => c1}
        val body = pa.predicateBody(c.program).get /* Only non-abstract predicates can be unfolded */
        produce(σ \ h1 /*\ insγ*/, s => snap.convert(s), tPerm, body, pve, c1)((σ2, c2) =>
          Q(σ2 /*\ σ.γ*/, c2))})
    }
  }
}
