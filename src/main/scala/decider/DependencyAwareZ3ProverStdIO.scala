package viper.silicon.decider

import viper.silicon.dependencyAnalysis._
import viper.silicon.interfaces.decider.DependencyAnalysisProverFeatures
import viper.silicon.state.IdentifierFactory
import viper.silver.reporter.Reporter

class DependencyAwareZ3ProverStdIO(uniqueId: String,
                                   termConverter: TermToSMTLib2Converter,
                                   identifierFactory: IdentifierFactory,
                                   reporter: Reporter) extends Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter) with DependencyAnalysisProverFeatures {

  protected var preambleDependencyAnalyzer: DependencyAnalyzer = new DefaultDependencyAnalyzer(None)

}
