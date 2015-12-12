/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.PartialVerificationError
import viper.silicon.{Map, toMap}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.{VerificationResult, Consumer, Producer, Evaluator}
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms._

class PredicateData(predicate: ast.Predicate)
                   (private val symbolConvert: SymbolConvert) {

  val argumentSorts = predicate.formalArgs map (fm => symbolConvert.toSort(fm.typ))

  val triggerFunction =
    Function(s"${predicate.name}%trigger", sorts.Snap +: argumentSorts, sorts.Bool)
}

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
  protected val symbolConverter: SymbolConvert

  import stateFactory._

  object predicateSupporter extends StatefulComponent {
    private type C = DefaultContext[H]
    private type CH = Chunk

    private var program: ast.Program = null
    private var predicateData: Map[ast.Predicate, PredicateData] = Map.empty

    def data = predicateData

    def handlePredicates(program: ast.Program): Unit = {
      analyze(program)
      declareFunctions()
    }

    private def analyze(program: ast.Program): Unit = {
      this.program = program

      this.predicateData = toMap(
        program.predicates map (pred => pred -> new PredicateData(pred)(symbolConverter)))
    }

    private def declareFunctions(): Unit = {
      predicateData.values foreach (data =>
        decider.prover.declare(FunctionDecl(data.triggerFunction)))
    }

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
          case _: QuantifiedChunk => None
          case _: MagicWandChunk => None}
        decider.assume(FApp(predicateData(predicate).triggerFunction, snap, tArgs))
        val ch = DirectPredicateChunk(predicate.name, tArgs, snap/*.convert(sorts.Snap)*/, tPerm, ncs)
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
        val body = pa.predicateBody(c.program).get /* Only non-abstract predicates can be unfolded */
        produce(σ \ h1 /*\ insγ*/, s => snap.convert(s), tPerm, body, pve, c1)((σ2, c2) => {
          decider.assume(FApp(predicateData(predicate).triggerFunction, snap, tArgs))
          Q(σ2 /*\ σ.γ*/, c2)})})
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      program = null
      predicateData = predicateData.empty
    }

    def stop() {}
  }
}
