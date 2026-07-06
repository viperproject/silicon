package viper.silicon.dependencyAnalysis.siliconComponents

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.dependencyAnalysis.DependencyAnalysisAxiomInfo
import viper.silicon.state.terms.Term
import viper.silicon.verifier.{MainVerifier, VerificationPoolManager}

class DependencyAwareVerificationPoolManager(mainVerifier: MainVerifier) extends VerificationPoolManager(mainVerifier) {

  override def pooledVerifiers: DefaultPooledVerifiers with DependencyAnalysisProverFeatures = DependencyAwarePooledVerifiers

  private object DependencyAwarePooledVerifiers extends DefaultPooledVerifiers with DependencyAnalysisProverFeatures {
    override def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit =
      workerVerifiers foreach {
        case daV: DependencyAnalysisAwareWorkerVerifier => daV.decider.prover.assumeAxiomsWithAnalysisInfo(axioms, description)
        case _ => super.assumeAxioms(axioms.map(_._1), description)
      }
  }
}
