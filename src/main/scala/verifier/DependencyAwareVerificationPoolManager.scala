package viper.silicon.verifier

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.dependencyAnalysis.{DefaultDependencyAnalyzer, DependencyAnalysisAxiomInfo, DependencyAnalyzer}
import viper.silicon.interfaces.decider.DependencyAnalysisProverLikeFeatures
import viper.silicon.state.terms.Term

class DependencyAwareVerificationPoolManager(mainVerifier: MainVerifier) extends VerificationPoolManager(mainVerifier) {

	override def pooledVerifiers: DefaultPooledVerifiers with DependencyAnalysisProverLikeFeatures = DependencyAwarePooledVerifiers

	private[verifier] object DependencyAwarePooledVerifiers extends DefaultPooledVerifiers with DependencyAnalysisProverLikeFeatures {
		override def assumeAxiomsWithAnalysisInfo(axioms: InsertionOrderedSet[(Term, DependencyAnalysisAxiomInfo)], description: String): Unit =
			workerVerifiers foreach (wv => wv match {
				case daV: DependencyAwareWorkerVerifier => daV.decider.prover.assumeAxiomsWithAnalysisInfo(axioms, description)
				case _ => super.assumeAxioms(axioms.map(_._1), description)
			})

		override protected var preambleDependencyAnalyzer: DependencyAnalyzer = new DefaultDependencyAnalyzer(None)
	}
}
