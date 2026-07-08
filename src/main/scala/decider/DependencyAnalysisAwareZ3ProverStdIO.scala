// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.decider

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugAxiom
import viper.silicon.dependencyAnalysis.{DefaultDependencyAnalyzer, DependencyAnalysisAxiomInfo, DependencyAnalysisNode, DependencyAnalyzer}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms.Term
import viper.silver.reporter.Reporter

class DependencyAnalysisAwareZ3ProverStdIO(uniqueId: String, termConverter: TermToSMTLib2Converter, identifierFactory: IdentifierFactory, reporter: Reporter)
  extends Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter) with DependencyAnalysisProverFeatures

trait DependencyAnalysisProverFeatures extends ProverLike {
  protected val preambleDependencyAnalyzer: DependencyAnalyzer = new DefaultDependencyAnalyzer(None)

  def getPreambleAnalysisNodes: Iterable[DependencyAnalysisNode] = preambleDependencyAnalyzer.getNodes

  def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit = {
    if (debugMode)
      preambleAssumptions :+= new DebugAxiom(description, axioms.map(_._1))

    axioms.foreach(axiom => {
      val analysisAxiomInfo = axiom._2
      if (analysisAxiomInfo.analysisInfos.analysisEnabled) {
        val id = preambleDependencyAnalyzer.addAxiom(axiom._1, analysisAxiomInfo)
        assume(axiom._1, DependencyAnalyzer.createAxiomLabel(id))
      } else {
        assume(axiom._1, "")
      }
    })
  }
}

