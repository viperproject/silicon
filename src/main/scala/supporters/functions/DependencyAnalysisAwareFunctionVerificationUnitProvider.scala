// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.dependencyAnalysis.{DependencyAnalysisAxiomInfo, DependencyAnalyzer}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, True, Var}
import viper.silicon.verifier.DependencyAnalysisAwareVerifier
import viper.silver.ast

trait DependencyAnalysisAwareFunctionVerificationUnitProvider extends DefaultFunctionVerificationUnitProvider { v: DependencyAnalysisAwareVerifier =>

  override def functionsSupporter: FunctionsSupporter = DependencyAnalysisAwareFunctionSupporter

  object DependencyAnalysisAwareFunctionSupporter extends FunctionsSupporter {
    override protected def handleFunction(sInit: State, function: ast.Function): VerificationResult = {

      addPreconditionNodes(function.pres)

      val result = super.handleFunction(sInit, function)

      if (function.body.isEmpty) {
        decider.getDependencyAnalyzer.addNodes(decider.prover.getPreambleAnalysisNodes)
        addDependenciesForAbstractMember(function.pres, function.posts)
      }

      attachIntraproceduralResult(result, function)

      result
    }

    override protected def emitAndRecordFunctionAxioms(axiom: (Term, DependencyAnalysisAxiomInfo)*): Unit = {
      val cleanAxiom = axiom.map(a => (a._1.transform {
        case v: Var if DependencyAnalyzer.isAnalysisLabel(v) => True // replace dependency analysis labels by True to avoid errors
      }(), a._2))
      decider.prover.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(cleanAxiom), "Function axioms")

      emittedFunctionAxiomsWithInfo = emittedFunctionAxiomsWithInfo ++ cleanAxiom
    }

    override def emitAxiomsAfterVerification(sink: ProverLike): Unit =
      sink.assumeAxiomsWithAnalysisInfo(InsertionOrderedSet(emittedFunctionAxiomsWithInfo), "Function axioms")

  }

}
