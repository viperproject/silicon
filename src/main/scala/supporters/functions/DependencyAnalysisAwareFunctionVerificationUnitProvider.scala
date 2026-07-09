// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.DependencyAnalysisProverFeatures
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.dependencyAnalysis.{DependencyAnalysisAxiomInfo, DependencyAnalyzer, SimpleAssertionNode}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, True, Var}
import viper.silicon.verifier.{DependencyAnalysisAwareVerifier, Verifier}
import viper.silver.ast
import viper.silver.dependencyAnalysis._

trait DependencyAnalysisAwareFunctionVerificationUnitProvider extends DefaultFunctionVerificationUnitProvider { v: DependencyAnalysisAwareVerifier =>

  override def functionsSupporter: FunctionsSupporter = DependencyAnalysisAwareFunctionSupporter

  object DependencyAnalysisAwareFunctionSupporter extends FunctionsSupporter {
    override protected def handleFunction(sInit: State, function: ast.Function): VerificationResult = {

      val presAssertionNodeForJoin = function.pres.flatMap(_.topLevelConjuncts).map(pc => SimpleAssertionNode(True, AnalysisSourceInfo.createAnalysisSourceInfo(pc), AssumptionType.Precondition, SimpleDependencyAnalysisMerge(AnalysisSourceInfo.createAnalysisSourceInfo(pc)), List(SimpleDependencyAnalysisJoin(AnalysisSourceInfo.createAnalysisSourceInfo(pc), JoinType.Sink, EdgeType.Up)), function.name))
      presAssertionNodeForJoin foreach decider.getDependencyAnalyzer.addAssertionNode

      val result = super.handleFunction(sInit, function)

      if (function.body.isEmpty) {
        decider.getDependencyAnalyzer.addNodes(decider.prover.getPreambleAnalysisNodes)
        decider.getDependencyAnalyzer.addDependenciesForAbstractMembers(function.pres.flatMap(_.topLevelConjuncts), function.posts.flatMap(_.topLevelConjuncts), decider.defaultAnalysisInfos)
      }

      val allErrors = (result :: result.previous.toList).filter(_.isInstanceOf[Failure]).map(_.asInstanceOf[Failure])
      result.dependencyGraphInterpreter = decider.getDependencyAnalyzer.buildFinalGraph().map(new DependencyGraphInterpreter(function.name, _,
        allErrors, Some(function)))

      result
    }

    override protected def emitAndRecordFunctionAxioms(axiom: (Term, DependencyAnalysisAxiomInfo)*): Unit = {
      val cleanAxiom =
        if (!Verifier.config.enableDependencyAnalysis()) axiom
        else axiom.map(a => (a._1.transform {
          case Var(name, _, _) if name.name.startsWith(DependencyAnalyzer.analysisLabelName) => True // replace dependency analysis labels by True to avoid errors
        }(), a._2))
      decider.prover.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(cleanAxiom), "Function axioms")

      emittedFunctionAxiomsWithInfo = emittedFunctionAxiomsWithInfo ++ cleanAxiom
    }

    override def emitAxiomsAfterVerification(sink: ProverLike): Unit = sink match {
      case daSink: DependencyAnalysisProverFeatures =>
        daSink.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(emittedFunctionAxiomsWithInfo), "Function axioms")
      case _ => super.emitAxiomsAfterVerification(sink)
    }

  }

}
