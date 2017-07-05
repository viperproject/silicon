/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import ch.qos.logback.classic.Logger
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.decider.Decider
import viper.silicon.{Map, SymbExLogger, toMap}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state._
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms._
import viper.silicon.interfaces._
import viper.silicon.rules.executionFlowController
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.freshSnap

class PredicateData(predicate: ast.Predicate)
                   /* Note: Holding a reference to a fixed symbol converter (instead of going
                    *       through a verifier) is only safe if the converter is effectively
                    *       independent of the verifiers.
                    */
                   (private val symbolConvert: SymbolConverter) {

  val argumentSorts = predicate.formalArgs map (fm => symbolConvert.toSort(fm.typ))

  val triggerFunction =
    Fun(Identifier(s"${predicate.name}%trigger"), sorts.Snap +: argumentSorts, sorts.Bool)
}

trait PredicateVerificationUnit
    extends VerifyingPreambleContributor[Sort, Fun, Term, ast.Predicate] {

  def data: Map[ast.Predicate, PredicateData]
}

trait DefaultPredicateVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider
  def symbolConverter: SymbolConverter

  object predicateSupporter extends PredicateVerificationUnit with StatefulComponent {
    import viper.silicon.rules.producer._

    private var predicateData: Map[ast.Predicate, PredicateData] = Map.empty

    def data = predicateData
    def units = predicateData.keys.toSeq

    /* Preamble contribution */

    def analyze(program: Program): Unit = {
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

    def updateGlobalStateAfterAnalysis(): Unit = {
      Verifier.predicateData = predicateData
    }

    /* Verification and subsequent preamble contribution */

    def verify(sInit: State, predicate: ast.Predicate): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

      SymbExLogger.insertMember(predicate, null, v.decider.pcs)

      val ins = predicate.formalArgs.map(_.localVar)
      val s = sInit.copy(g = Store(ins.map(x => (x, decider.fresh(x)))),
                         h = Heap(),
                         oldHeaps = OldHeaps())
      val err = PredicateNotWellformed(predicate)

      val result = predicate.body match {
        case None =>
          Success()
        case Some(body) =>
          /*    locallyXXX {
                magicWandSupporter.checkWandsAreSelfFraming(σ.γ, σ.h, predicate, c)}
          &&*/  executionFlowController.locally(s, v)((s1, _) => {
                  produce(s1, freshSnap, body, err, v)((_, _) =>
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

    def contributeToGlobalStateAfterVerification(): Unit = {
      Verifier.predicateData = predicateData
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      predicateData = predicateData.empty
    }

    def stop() {}
  }
}
