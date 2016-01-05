/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors._
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.{Set, Map, toMap}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms._

class PredicateData(predicate: ast.Predicate)
                   (private val symbolConvert: SymbolConvert) {

  val argumentSorts = predicate.formalArgs map (fm => symbolConvert.toSort(fm.typ))

  val triggerFunction =
    Fun(Identifier(s"${predicate.name}%trigger"), sorts.Snap +: argumentSorts, sorts.Bool)
}

trait PredicateSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         S <: State[ST, H, S],
                         C <: Context[C]]
    extends VerificationUnit[H, ast.Predicate] {

  def data: Map[ast.Predicate, PredicateData]

  def fold(σ: S,
           predicate: ast.Predicate,
           tArgs: List[Term],
           tPerm: Term,
           pve: PartialVerificationError,
           c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult

  def unfold(σ: S,
             predicate: ast.Predicate,
             tArgs: List[Term],
             tPerm: Term,
             pve: PartialVerificationError,
             c: C,
             pa: ast.PredicateAccess /* TODO: Make optional (as in magicWandSupporter.foldingPredicate) */)
            (Q: (S, C) => VerificationResult)
            : VerificationResult
}

trait PredicateSupporterProvider[ST <: Store[ST],
                                 H <: Heap[H],
                                 S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[ST, H, S, DefaultContext[H]]
            with ChunkSupporterProvider[ST, H, S]
            with MagicWandSupporter[ST, H, S] =>

  private type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, DefaultContext[H]]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val symbolConverter: SymbolConvert

  import decider.{fresh, locally}
  import stateFactory._

  object predicateSupporter extends PredicateSupporter[ST, H, S, C] {
    private var program: ast.Program = null
    private var predicateData: Map[ast.Predicate, PredicateData] = Map.empty

    def analyze(program: Program): Unit = {
      this.program = program

      this.predicateData = toMap(
        program.predicates map (pred => pred -> new PredicateData(pred)(symbolConverter)))
    }

    def data = predicateData
    def units = predicateData.keys.toSeq

    def sorts: Set[Sort] = Set.empty
    def declareSorts(): Unit = { /* No sorts need to be declared */ }

    def declareSymbols(): Unit = {
      decider.prover.logComment("Declaring predicate trigger functions")
      predicateData.values foreach (data =>
        decider.prover.declare(FunctionDecl(data.triggerFunction)))
    }

    def verify(predicate: ast.Predicate, c: DefaultContext[H]): Seq[VerificationResult] = {
      log.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
      decider.prover.logComment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

      val ins = predicate.formalArgs.map(_.localVar)

      val γ = Γ(ins.map(v => (v, fresh(v))))
      val σ = Σ(γ, Ø, Ø)
      val err = PredicateNotWellformed(predicate)

      val result = predicate.body match {
        case None =>
          Success()
        case Some(body) => (
                locally {
                  magicWandSupporter.checkWandsAreSelfFraming(σ.γ, σ.h, predicate, c)}
            &&  locally {
                  produce(σ, decider.fresh, terms.FullPerm(), body, err, c)((_, c1) =>
                    Success())})
      }

      Seq(result)
    }

    def emitAxioms(): Unit = { /* No axioms need to be emitted */ }

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
      val c0 = c.copy(fvfAsSnap = true)
      consume(σ \ insγ, tPerm, body, pve, c0)((σ1, snap, c1) => {
        decider.assume(App(predicateData(predicate).triggerFunction, snap +: tArgs))
        val ch = PredicateChunk(predicate.name, tArgs, snap/*.convert(sorts.Snap)*/, tPerm)
        val c2 = c1.copy(fvfAsSnap = c.fvfAsSnap)
        val (h1, c3) = chunkSupporter.produce(σ1, σ1.h, ch, c2)
        Q(σ \ h1, c3)})
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
      chunkSupporter.consume(σ, σ.h, predicate.name, tArgs, tPerm, pve, c, pa)((h1, snap, c1) => {
        val body = pa.predicateBody(c.program).get /* Only non-abstract predicates can be unfolded */
        produce(σ \ h1 /*\ insγ*/, s => snap.convert(s), tPerm, body, pve, c1)((σ2, c2) => {
          decider.assume(App(predicateData(predicate).triggerFunction, snap +: tArgs))
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
