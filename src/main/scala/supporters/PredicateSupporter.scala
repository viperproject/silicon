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
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.{Map, toMap}
import viper.silicon.interfaces.decider.{Decider, ProverLike}
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.SymbExLogger
import viper.silicon.interfaces._
import viper.silicon.supporters.qps.QuantifiedPredicateChunkSupporterProvider

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
    extends VerifyingPreambleContributor[Sort, Fun, Term, H, ast.Predicate] {

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
            with QuantifiedPredicateChunkSupporterProvider[ST, H, S]
            with MagicWandSupporter[ST, H, S] =>

  private type C = DefaultContext[H]

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  protected val decider: Decider[ST, H, S, DefaultContext[H]]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val symbolConverter: SymbolConvert

  import decider.{fresh, locally}
  import stateFactory._

  object predicateSupporter extends PredicateSupporter[ST, H, S, C] {
    /*private*/ var program: ast.Program = _
    /*private*/ var predicateData: Map[ast.Predicate, PredicateData] = Map.empty

    def data = predicateData
    def units = predicateData.keys.toSeq

    /* Preamble contribution */

    def analyze(program: Program): Unit = {
      this.program = program

      this.predicateData = toMap(
        program.predicates map (pred => pred -> new PredicateData(pred)(symbolConverter)))
    }

    /* Predicate supporter generates no sorts */
    val sortsAfterAnalysis: Iterable[Sort] = Seq.empty
    def declareSortsAfterAnalysis(sink: ProverLike): Unit = ()

    def symbolsAfterAnalysis: Iterable[Fun] = {
      predicateData.values map (_.triggerFunction)
    }

    def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
      sink.comment("Declaring predicate trigger functions")
      symbolsAfterAnalysis foreach (f => sink.declare(FunctionDecl(f)))
    }

    /* Predicate supporter generates no axioms */
    val axiomsAfterAnalysis: Iterable[Term] = Seq.empty
    def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = ()

    /* Verification and subsequent preamble contribution */

    def verify(predicate: ast.Predicate, c: DefaultContext[H]): Seq[VerificationResult] = {
      log.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

      SymbExLogger.insertMember(predicate, Σ(Ø, Ø, Ø), decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]])

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
                  produce(σ, decider.fresh, body, err, c)((_, _) =>
                    Success())})
      }

      Seq(result)
    }

    /* Predicate supporter generates no sorts */
    val sortsAfterVerification: Iterable[Sort] = Seq.empty
    def declareSortsAfterVerification(sink: ProverLike): Unit = ()

    /* Predicate supporter does not generate additional symbols during verification */
    val symbolsAfterVerification: Iterable[Fun] = Seq.empty
    def declareSymbolsAfterVerification(sink: ProverLike): Unit = ()

    /* Predicate supporter generates no axioms */
    val axiomsAfterVerification: Iterable[Term] = Seq.empty
    def emitAxiomsAfterVerification(sink: ProverLike): Unit = ()

    /* Other predicate-related operations */

    def fold(σ: S, predicate: ast.Predicate, tArgs: List[Term], tPerm: Term, pve: PartialVerificationError, c: C)
            (Q: (S, C) => VerificationResult)
            : VerificationResult = {

      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
      val insγ = σ.γ + Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      val c0 = c.copy(fvfAsSnap = true).scalePermissionFactor(tPerm)
      consume(σ \ insγ, body, pve, c0)((σ1, snap, c1) => {
        decider.assume(App(predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
          if (c.qpPredicates.contains(predicate)) {
            //convert snapshot to desired type if necessary
            val snapConvert = snap.convert(c1.predicateSnapMap(predicate))
            val formalArgs = predicate.formalArgs.map(formalArg => Var(Identifier(formalArg.name), symbolConverter.toSort(formalArg.typ)))
            val (psf, optPsfDef) = quantifiedPredicateChunkSupporter.createSingletonPredicateSnapFunction(predicate, tArgs, formalArgs, snapConvert, c)
            optPsfDef.foreach(psfDef => decider.assume(psfDef.domainDefinitions ++ psfDef.snapDefinitions))
            //create single quantified predicate chunk with given snapshot
            val ch = quantifiedPredicateChunkSupporter.createSingletonQuantifiedPredicateChunk(tArgs, formalArgs, predicate.name, psf, tPerm)
            val σ2 = σ1 \ σ.γ \+ ch
            Q(σ2 , c1)
          } else {
            val ch = PredicateChunk(predicate.name, tArgs, snap/*.convert(sorts.Snap)*/, tPerm)
            val c2 = c1.copy(fvfAsSnap = c.fvfAsSnap,
                             permissionScalingFactor = c.permissionScalingFactor)
            val (h1, c3) = chunkSupporter.produce(σ1, σ1.h, ch, c2)
            Q(σ \ h1, c3)
          }
      })
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

      /* [2016-05-09 Malte] The comment below appears to no longer be valid (in
       * Silicon revision aa8932f340ca). It is not unlikely that the originally
       * observed issue was actually caused by a different problem, because the
       * predicate body (with the formal predicate argument bound to some term)
       * does not occur in any heap-dependent function, and thus does not need to
       * be translated.
       *
       * [2014-12-10 Malte] Changing the store (insγ) doesn't play nicely with the
       * snapshot recorder because it might result in the same local variable
       * being bound to different terms, e.g., in the case of fun3 at the end of
       * functions/unfolding.sil, where the formal predicate argument x is bound
       * to y and y.n.
       */

      val insγ = σ.γ + Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
      val c0 = c.scalePermissionFactor(tPerm)
      if (c.qpPredicates.contains(predicate)) {
       val formalVars:Seq[Var] = c.predicateFormalVarMap(predicate)
        val hints = quantifiedPredicateChunkSupporter.extractHints(None, None, tArgs)
        val chunkOrderHeuristics = quantifiedPredicateChunkSupporter.hintBasedChunkOrderHeuristic(hints)
        //remove permission for single predicate
        quantifiedPredicateChunkSupporter.splitSingleLocation(σ, σ.h, predicate, tArgs, formalVars, PermTimes(tPerm, tPerm), chunkOrderHeuristics, c) {
          case Some((h1, ch, psfDef, c2)) =>
            val psfDomain = if (c2.fvfAsSnap) psfDef.domainDefinitions else Seq.empty
            decider.assume(psfDomain ++ psfDef.snapDefinitions)
            //evaluate snapshot value
            val snap = ch.valueAt(tArgs)
            produce(σ \ h1 \ insγ, s => snap.convert(s), body, pve, c2)((σ2, c3) => {
              decider.assume(App(predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
              Q(σ2 \ σ.γ, c3)})

          case None => Failure(pve dueTo InsufficientPermission(pa))
        }
      } else {
        /*
        chunkSupporter.consume(σ, σ.h, predicate.name, tArgs, tPerm, pve, c, pa)((h1, snap, c1) => {
          produce(σ \ h1 \ insγ, s => snap.convert(s), tPerm, body, pve, c1)((σ2, c2) => {
            decider.assume(App(predicateData(predicate).triggerFunction, snap +: tArgs))
            Q(σ2 \ σ.γ, c2)})})*/
        chunkSupporter.consume(σ, σ.h, predicate.name, tArgs, c0.permissionScalingFactor, pve, c0, pa)((h1, snap, c1) => {
          produce(σ \ h1 \ insγ, s => snap.convert(s), body, pve, c1)((σ2, c2) => {
            decider.assume(App(predicateData(predicate).triggerFunction, snap +: tArgs))
            val c3 = c2.copy(permissionScalingFactor = c.permissionScalingFactor)
            Q(σ2 \ σ.γ, c3)})})
      }
    }

/* NOTE: Possible alternative to storing the permission scaling factor in the context
 *       or passing it to produce/consume as an explicit argument.
 *       Carbon uses Permissions.multiplyExpByPerm as well (but does not extend the
 *       store).
 */
//    private def scale(γ: ST, body: ast.Exp, perm: Term) = {
//      /* TODO: Ensure that variable name does not clash with any Silver identifier already in use */
//      val scaleFactorVar = ast.LocalVar(identifierFactory.fresh("p'unf").name)(ast.Perm)
//      val scaledBody = ast.utility.Permissions.multiplyExpByPerm(body, scaleFactorVar)
//
//      (γ + (scaleFactorVar -> perm), scaledBody)
//    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      program = null
      predicateData = predicateData.empty
    }

    def stop() {}
  }
}
