// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.Verifier

import java.nio.file.Path

class KInductionEval1 extends SilSuite {
  private val siliconTestDirectories =
    Seq("kinduct_eval")

  private val silTestDirectories = Seq()
    //Seq("all",
    //    "quantifiedpermissions", "quantifiedpredicates", "quantifiedcombinations",
    //    "wands", "termination", "refute",
    //    "examples")

  val testDirectories: Seq[String] = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]): SiliconFrontend = {
    require(files.length == 1, "tests should consist of exactly one file")

    val fe = new SiliconFrontend(NoopReporter)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation): Boolean = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) => issue != 34
      case _ => false
    }
  }

  val silicon: Silicon = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    new Silicon(reporter, debugInfo)
  }

  def verifiers: Seq[Silicon] = Seq(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    silicon.parseCommandLine(commandLineArguments ++ args :+ Silicon.dummyInputFilename)
  }

  val commandLineArguments: Seq[String] =
    Seq("--timeout", "60" /* seconds */, "--enableMoreCompleteExhale", "--enableKInduction=1", "--prover=Z3-API")
}
