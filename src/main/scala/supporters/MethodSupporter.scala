// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silicon.dependencyAnalysis.{DependencyGraphInterpreter, DependencyAnalyzer, AssumptionType}
import viper.silicon.decider.Decider
import viper.silicon.interfaces._
import viper.silicon.logger.records.data.WellformednessCheckRecord
import viper.silicon.rules.{consumer, executionFlowController, executor, producer}
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.{Map, toMap}
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.reporter.AnnotationWarning
import viper.silver.verifier.errors._

/* TODO: Consider changing the DefaultMethodVerificationUnitProvider into a SymbolicExecutionRule */

trait MethodVerificationUnit extends VerificationUnit[ast.Method]

trait DefaultMethodVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider

  object methodSupporter extends MethodVerificationUnit with StatefulComponent {
    import consumer._
    import executor._
    import producer._

    private var _units: Seq[ast.Method] = _

    def analyze(program: ast.Program): Unit = {
      _units = program.methods
    }

    def units = _units

    def verify(sInit: State, method: ast.Method): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, method.name, "-" * 10))

      val proverOptions: Map[String, String] = method.info.getUniqueInfo[ast.AnnotationInfo] match {
        case Some(ai) if ai.values.contains("proverArgs") =>
          toMap(ai.values("proverArgs").flatMap(o => {
            val index = o.indexOf("=")
            if (index == -1) {
              reporter report AnnotationWarning(s"Invalid proverArgs annotation ${o} on method ${method.name}. " +
                s"Required format for each option is optionName=value.")
              None
            } else {
              val (name, value) = (o.take(index), o.drop(index + 1))
              Some((name, value))
            }
          }))
        case _ =>
          Map.empty
      }
      v.decider.setProverOptions(proverOptions)

      openSymbExLogger(method)

      val pres = method.pres
      val posts = method.posts

      val body = method.bodyOrAssumeFalse.toCfg()
        /* TODO: Might be worth special-casing on methods with empty bodies */

      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

      val ins = method.formalArgs.map(_.localVar)
      val outs = method.formalReturns.map(_.localVar)

      val g = Store(   ins.map(x => (x, decider.fresh(x)))
                    ++ outs.map(x => (x, decider.fresh(x)))
                    ++ method.scopedDecls.collect { case l: ast.LocalVarDecl => l }.map(_.localVar).map(x => (x, decider.fresh(x))))

      val s = sInit.copy(g = g,
                         h = Heap(),
                         oldHeaps = OldHeaps(),
                         methodCfg = body)

      if (Verifier.config.printMethodCFGs()) {
        viper.silicon.common.io.toFile(
          body.toDot,
          new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.dot"))
      }

      val annotatedAssumptionTypeOpt = DependencyAnalyzer.extractAssumptionTypeFromInfo(method.info)
      val postConditionType = annotatedAssumptionTypeOpt.getOrElse(if(method.body.isDefined) AssumptionType.ImplicitPostcondition else AssumptionType.ExplicitPostcondition)

      errorsReportedSoFar.set(0)
      val result =
        /* Combined the well-formedness check and the execution of the body, which are two separate
         * rules in Smans' paper.
         */
        executionFlowController.locally(s, v)((s1, v1) => {
          produces(s1, freshSnap, pres, ContractNotWellformed, v1, annotatedAssumptionTypeOpt.getOrElse(AssumptionType.Precondition))((s2, v2) => {
            v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
            val s2a = s2.copy(oldHeaps = s2.oldHeaps + (Verifier.PRE_STATE_LABEL -> s2.h))
            (  executionFlowController.locally(s2a, v2)((s3, v3) => {
                  val s4 = s3.copy(h = Heap())
                  val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
                  val sepIdentifier = symbExLog.openScope(impLog)
                  produces(s4, freshSnap, posts, ContractNotWellformed, v3, annotatedAssumptionTypeOpt.getOrElse(postConditionType))((_, _) => {
                    symbExLog.closeScope(sepIdentifier)
                    Success()})})
            && {
               executionFlowController.locally(s2a, v2)((s3, v3) =>  {
                 val da = v3.decider.dependencyAnalyzer
                 if(method.body.isEmpty) v3.decider.removeDependencyAnalyzer()
                  exec(s3, body, v3)((s4, v4) => {
                    if(method.body.isEmpty) v3.decider.dependencyAnalyzer = da
                    consumes(s4, posts, false, postViolated, v4, postConditionType)((_, _, _) =>
                      Success())})}) }  )})})

      if(method.body.isEmpty){
        v.decider.dependencyAnalyzer.addCustomExpDependency(method.pres.flatMap(_.topLevelConjuncts), method.posts.flatMap(_.topLevelConjuncts))
      }

      result.dependencyGraphInterpreter = v.decider.dependencyAnalyzer.buildFinalGraph().map(new DependencyGraphInterpreter(method.name, _, Some(method)))
      result.dependencyGraphInterpreter.foreach(_.initJoinCandidateNodes())

      v.decider.resetProverOptions()

      symbExLog.closeMemberScope()
      Seq(result)
    }

    /* Lifetime */

    def start(): Unit = {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop(): Unit = {}
  }
}
