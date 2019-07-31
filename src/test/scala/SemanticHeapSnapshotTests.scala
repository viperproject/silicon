// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Path

import scala.io.Source

import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}
import viper.silver.parser.FastParser
import viper.silver.plugin.SilverPluginManager
import fastparse.core.Parsed
import viper.silicon.{Silicon, SiliconFrontend, SymbExLogger}
import viper.silver.frontend.DefaultStates
import viper.silver.reporter.NoopReporter

class SemanticHeapSnapshotTests extends SilSuite {
  private val siliconTestDirectories = Seq("consistency", "issue387")
  private val silTestDirectories = Seq("all", "quantifiedpermissions", "wands", "examples", "quantifiedpredicates" ,"quantifiedcombinations")
  val testDirectories = siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")
	val sourceCode = Source.fromFile(files(0).toString).getLines.mkString
	val plugins = SilverPluginManager()
	plugins.beforeParse(sourceCode, false) match {
		case Some(inputPlugin) => {
			val result = FastParser.parse(inputPlugin, files(0))
			result match {
			 case Parsed.Success(x,y) => { println(x,y) }
			}
		}
	}

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    SymbExLogger.reset()
    SymbExLogger.filePath = files.head
    SymbExLogger.initUnitTestEngine()
    val fe = new SiliconFrontend(NoopReporter)//SiliconFrontendWithUnitTesting()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation) = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) => issue != 34
      case _ => false
    }
  }

  lazy val verifiers = List(createSiliconInstance())

  val commandLineArguments: Seq[String] = Seq.empty

  private def createSiliconInstance() = {
    val args =
      commandLineArguments ++
      Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }
}

