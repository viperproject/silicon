// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.dependencyAnalysis.{DependencyAnalysisInfos, SimpleAssertionNode}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state.State
import viper.silicon.state.terms.True
import viper.silicon.verifier.DependencyAnalysisAwareVerifier
import viper.silver.ast.Method
import viper.silver.dependencyAnalysis._

trait DependencyAnalysisAwareMethodVerificationUnitProvider extends DefaultMethodVerificationUnitProvider { v: DependencyAnalysisAwareVerifier =>
  override def methodSupporter: MethodSupporter = DependencyAnalysisAwareMethodSupporter

  private object DependencyAnalysisAwareMethodSupporter extends MethodSupporter {

    override def verify(sInit: State, method: Method): Seq[VerificationResult] = {

      val presAssertionNodeForJoin = method.pres.flatMap(_.topLevelConjuncts).map(pc => SimpleAssertionNode(True, AnalysisSourceInfo.createAnalysisSourceInfo(pc), AssumptionType.Precondition, SimpleDependencyAnalysisMerge(AnalysisSourceInfo.createAnalysisSourceInfo(pc)), List(SimpleDependencyAnalysisJoin(AnalysisSourceInfo.createAnalysisSourceInfo(pc), JoinType.Sink, EdgeType.Up)), method.name))
      presAssertionNodeForJoin foreach decider.getDependencyAnalyzer.addAssertionNode

      val result = super.verify(sInit, method)

      if (method.body.isEmpty)
        decider.getDependencyAnalyzer.addDependenciesForAbstractMembers(method.pres.flatMap(_.topLevelConjuncts), method.posts.flatMap(_.topLevelConjuncts), DependencyAnalysisInfos.DefaultDependencyAnalysisInfos)

      result foreach (r => {
        val allErrors = (r :: r.previous.toList).filter(_.isInstanceOf[Failure]).map(_.asInstanceOf[Failure])
        r.dependencyGraphInterpreter = decider.getDependencyAnalyzer.buildFinalGraph().map(new DependencyGraphInterpreter(method.name, _, allErrors, Some(method)))
      })

      result
    }
  }

}
