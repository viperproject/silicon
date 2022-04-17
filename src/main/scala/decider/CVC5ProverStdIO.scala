// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.decider

import java.nio.file.{Path, Paths}

import viper.silicon.state.IdentifierFactory
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{DefaultDependency => SilDefaultDependency}
import viper.silver.reporter.Reporter
import viper.silicon.common.config.Version


object Cvc5ProverStdIO {
  val name = "cvc5"
  val minVersion = Version("1.0.0")
  val maxVersion = None
  val exeEnvironmentalVariable = "CVC5_EXE"
  val dependencies = Seq(SilDefaultDependency("cvc5", minVersion.version, "https://github.com/cvc5/cvc5"))
  val staticPreamble = "/cvc5config.smt2"
  val startUpArgs = Seq("--lang=smt2.6")
  val randomizeSeedsOptions = Seq("seed", "sat-random-seed")
}

class Cvc5ProverStdIO(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory,
                    reporter: Reporter)
    extends ProverStdIO(uniqueId, termConverter, identifierFactory, reporter) {
    
  val name = Cvc5ProverStdIO.name
  val minVersion = Cvc5ProverStdIO.minVersion
  val maxVersion = Cvc5ProverStdIO.maxVersion
  val exeEnvironmentalVariable = Cvc5ProverStdIO.exeEnvironmentalVariable
  val dependencies = Cvc5ProverStdIO.dependencies
  val staticPreamble = Cvc5ProverStdIO.staticPreamble
  val startUpArgs = Cvc5ProverStdIO.startUpArgs
  val randomizeSeedsOptions = Cvc5ProverStdIO.randomizeSeedsOptions

  // cvc5 does not support per-check timeouts after instantiation.
  protected def setTimeout(timeout: Option[Int]): Unit = {
  }

  protected def getProverPath(): Path = {
    Paths.get(Verifier.config.cvc5Exe)
  }
}
