package viper.silicon.verifier

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.DependencyAnalysisProverFeatures
import viper.silicon.dependencyAnalysis.DependencyAnalysisAxiomInfo
import viper.silicon.state.terms.Term

class DependencyAnalysisAwareVerificationPoolManager(mainVerifier: MainVerifier) extends VerificationPoolManager(mainVerifier) {

  override def pooledVerifiers: DefaultPooledVerifiers with DependencyAnalysisProverFeatures = DependencyAnalysisAwarePooledVerifiers

  private object DependencyAnalysisAwarePooledVerifiers extends DefaultPooledVerifiers with DependencyAnalysisProverFeatures {
    override def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit =
      workerVerifiers foreach {
        case daV: DependencyAnalysisAwareWorkerVerifier => daV.decider.prover.assumeAxiomsWithAnalysisInfo(axioms, description)
        case _ => super.assumeAxioms(axioms.map(_._1), description)
      }
  }
}
