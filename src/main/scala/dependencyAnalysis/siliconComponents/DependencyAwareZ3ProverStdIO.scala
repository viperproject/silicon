package viper.silicon.dependencyAnalysis.siliconComponents

import viper.silicon.decider.{TermToSMTLib2Converter, Z3ProverStdIO}
import viper.silicon.state.IdentifierFactory
import viper.silver.reporter.Reporter

class DependencyAwareZ3ProverStdIO(uniqueId: String,
                                   termConverter: TermToSMTLib2Converter,
                                   identifierFactory: IdentifierFactory,
                                   reporter: Reporter) extends Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter)
  with DependencyAnalysisProverFeatures
