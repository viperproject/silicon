// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.verifier

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.DependencyAnalysisProverHandler
import viper.silicon.dependencyAnalysis.{AxiomNodeRegistry, DependencyAnalysisAxiomInfo}
import viper.silicon.state.terms.Term

class DependencyAnalysisAwareVerificationPoolManager(mainVerifier: DependencyAnalysisAwareMainVerifier) extends VerificationPoolManager(mainVerifier) {
  override type Worker = DependencyAnalysisAwareWorkerVerifier

  override protected def createWorker(): DependencyAnalysisAwareWorkerVerifier = mainVerifier.createWorkerVerifier()

  override def pooledVerifiers: DefaultPooledVerifiers with DependencyAnalysisProverHandler = DependencyAnalysisAwarePooledVerifiers

  private object DependencyAnalysisAwarePooledVerifiers extends DefaultPooledVerifiers with DependencyAnalysisProverHandler {
    override protected def axiomNodeRegistry: AxiomNodeRegistry = mainVerifier.axiomNodeRegistry

    def assume(term: Term, label: Option[String]): Unit =
      workerVerifiers foreach (_.decider.prover.assume(term, label))

    override def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit =
      workerVerifiers foreach (_.decider.prover.assumeAxiomsWithAnalysisInfo(axioms, description))
  }
}
