// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.verifier

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.DependencyAnalysisProverFeatures
import viper.silicon.dependencyAnalysis.{DependencyAnalysisAxiomInfo, DependencyAnalysisNode}
import viper.silicon.state.terms.Term

class DependencyAnalysisAwareVerificationPoolManager(mainVerifier: MainVerifier) extends VerificationPoolManager(mainVerifier) {

  def getAllDAAxiomNodes: Seq[DependencyAnalysisNode] = workerVerifiers.flatMap(v => v.decider.prover match {
    case d: DependencyAnalysisProverFeatures => d.getPreambleAnalysisNodes
    case _ => Set.empty
  })

  override def pooledVerifiers: DefaultPooledVerifiers with DependencyAnalysisProverFeatures = DependencyAnalysisAwarePooledVerifiers

  private object DependencyAnalysisAwarePooledVerifiers extends DefaultPooledVerifiers with DependencyAnalysisProverFeatures {
    override def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit =
      workerVerifiers foreach {
        case daV: DependencyAnalysisAwareWorkerVerifier => daV.decider.prover.assumeAxiomsWithAnalysisInfo(axioms, description)
        case _ => super.assumeAxioms(axioms.map(_._1), description)
      }
  }
}
