package viper.silicon.decider

import viper.silicon.state.IdentifierFactory
import viper.silver.reporter.Reporter

class TraceGeneratingZ3ProverStdIO(uniqueId: String,
                                   termConverter: TermToSMTLib2Converter,
                                   identifierFactory: IdentifierFactory,
                                   reporter: Reporter)
  extends Z3ProverStdIO(uniqueId, termConverter, identifierFactory, reporter){

  override val startUpArgs = Z3ProverStdIO.startUpArgs ++ Seq("trace=true", "proof=true")
}
