// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.decider.Decider
import viper.silicon.{Map, toMap}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state._
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms._
import viper.silicon.interfaces._
import viper.silicon.rules.executionFlowController
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.freshSnap
import viper.silver.verifier.reasons.InternalReason

object PredicateHelper {
  def upperBound(pred: ast.Predicate): Option[ast.Exp] = {
    pred.info.getUniqueInfo[ast.AnnotationInfo] match {
      case Some(annInfo) => annInfo.values.get("bound") match {
        case Some(Seq(v)) =>
          try {
            val intVal = Integer.parseInt(v)
            Some(ast.IntLit(intVal)())
          } catch {
            case _: NumberFormatException => None
          }
        case _ => None
      }
      case _ => None
    }
  }
}

class PredicateData(predicate: ast.Predicate)
                   /* Note: Holding a reference to a fixed symbol converter (instead of going
                    *       through a verifier) is only safe if the converter is effectively
                    *       independent of the verifiers.
                    */
                   (private val symbolConvert: SymbolConverter) {

  val argumentSorts = predicate.formalArgs map (fm => symbolConvert.toSort(fm.typ))

  val triggerFunction =
    Fun(Identifier(s"${predicate.name}%trigger"), sorts.Snap +: argumentSorts, sorts.Bool)

  val upperBoundExp: Option[ast.Exp] = {
    val ub = PredicateHelper.upperBound(predicate)
    ub match {
      case Some(ub) =>
        require(symbolConvert.toSort(ub.typ) == sorts.Int, s"Permissions $ub must be of sort Int, but found ${symbolConvert.toSort(ub.typ)}")

      case None => ()
    }
    ub
  }
  var upperBoundTerm: Option[Term] = None
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

    /*private*/ var predicateData: Map[ast.Predicate, PredicateData] = Map.empty

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

    /* Verification and subsequent preamble contribution */

    def verify(sInit: State, predicate: ast.Predicate): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " PREDICATE " + predicate.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, predicate.name, "-" * 10))

      openSymbExLogger(predicate)

      val ins = predicate.formalArgs.map(_.localVar)
      val ubVar = ast.LocalVar("limit", ast.Perm)()
      val s = sInit.copy(g = Store(ins.map(x => (x, decider.fresh(x))) ++ Seq((ubVar, decider.fresh(ubVar)))),
                         h = Heap(),
                         oldHeaps = OldHeaps())
      val err = PredicateNotWellformed(predicate)
      val ubErr = PredicateNotWellformed(predicate)

      val result = predicate.body match {
        case None =>
          Success()
        case Some(body) =>
          /*    locallyXXX {
                magicWandSupporter.checkWandsAreSelfFraming(σ.γ, σ.h, predicate, c)}
          &&*/  executionFlowController.locally(s, v)((s1, _) => {
                  produce(s1, freshSnap, body, err, v)((_, _) =>
                    Success())}) && executionFlowController.locally(s, v)((s1, _) => {
          PredicateHelper.upperBound(predicate) match {
            case None =>
              Success()
            case Some(ubExp) =>
              val s3 = s1.scalePermissionFactor(s1.g(ubVar))
              produce(s3, freshSnap, ast.And(ast.PermGtCmp(ubVar, ubExp)(), body)(), ubErr, v)((s4, _) =>
                v.decider.assert(terms.False, s4, None) {
                  case true =>
                    Success()
                  case false =>
                    //Success()
                    Failure(ubErr.dueTo(InternalReason(predicate, "Incorrect upper bound")))
                })}})
      }

      symbExLog.closeMemberScope()
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

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      predicateData = predicateData.empty
    }

    def stop(): Unit = {}
  }
}
