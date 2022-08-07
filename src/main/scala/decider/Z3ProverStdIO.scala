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


object Z3ProverStdIO {
  val name = "Z3"
  val minVersion = Version("4.5.0")
  val maxVersion = None // Some(Version("4.5.0")) /* X.Y.Z if that is the *last supported* version */
  val exeEnvironmentalVariable = "Z3_EXE"
  val dependencies = Seq(SilDefaultDependency("Z3", minVersion.version, "https://github.com/Z3Prover/z3"))
  val staticPreamble = "/z3config.smt2"
  val startUpArgs = Seq("-smt2", "-in")
  val randomizeSeedsOptions = Seq("sat.random_seed", "nlsat.seed", "fp.spacer.random_seed", "smt.random_seed", "sls.random_seed")
}

class Z3ProverStdIO(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory,
                    reporter: Reporter)
    extends ProverStdIO(uniqueId, termConverter, identifierFactory, reporter) {
    
  val name = Z3ProverStdIO.name
  val minVersion = Z3ProverStdIO.minVersion
  val maxVersion = Z3ProverStdIO.maxVersion
  val exeEnvironmentalVariable = Z3ProverStdIO.exeEnvironmentalVariable
  val dependencies = Z3ProverStdIO.dependencies
  val staticPreamble = Z3ProverStdIO.staticPreamble
  val startUpArgs = Z3ProverStdIO.startUpArgs
  val randomizeSeedsOptions = Z3ProverStdIO.randomizeSeedsOptions

  protected def setTimeout(timeout: Option[Int]): Unit = {
    val effectiveTimeout = timeout.getOrElse(Verifier.config.proverTimeout)

    /* [2015-07-27 Malte] Setting the timeout unnecessarily often seems to
     * worsen performance, if only a bit. For the current test suite of
     * 199 Silver files, the total verification time increased from 60s
     * to 70s if 'set-option' is emitted every time.
     */
    if (lastTimeout != effectiveTimeout) {
      lastTimeout = effectiveTimeout

      if(Verifier.config.proverEnableResourceBounds) {
        writeLine(s"(set-option :rlimit ${effectiveTimeout * Verifier.config.proverResourcesPerMillisecond})")
      } else {
        writeLine(s"(set-option :timeout $effectiveTimeout)")
      }
      readSuccess()
    }
  }

  protected def getProverPath: Path = {
    Paths.get(Verifier.config.z3Exe)
  }

  override def emitSettings(contents: Iterable[String]): Unit = emit(contents)
}
