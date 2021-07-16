// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.Verifier

class SiliconTests extends SilSuite {
  private val siliconTestDirectories =
    Seq("consistency", "issue387", "heuristics")

  private val silTestDirectories =
    Seq("all",
        "quantifiedpermissions", "quantifiedpredicates" ,"quantifiedcombinations",
        "wands", "termination",
        "examples")

  val testDirectories: Seq[String] = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]): SiliconFrontend = {
    require(files.length == 1, "tests should consist of exactly one file")

    /* If needed, Silicon reads the filename of the program under verification from Verifier.inputFile.
    When the test suite is executed (sbt test/testOnly), Verifier.inputFile is set here. When Silicon is
    run from the command line, Verifier.inputFile is set in src/main/scala/Silicon.scala. */
    viper.silicon.verifier.Verifier.inputFile = Some(files.head)

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

  val silicon = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    new Silicon(reporter, debugInfo)
  }

  def verifiers = List(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]) = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    silicon.parseCommandLine(args :+ Silicon.dummyInputFilename)
  }

  val commandLineArguments: Seq[String] =
    Seq("--timeout", "300" /* seconds */)

}
