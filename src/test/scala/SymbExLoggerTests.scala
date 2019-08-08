// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.io.File
import java.nio.file.{Files, Path, Paths}

import viper.silicon.logger.SymbExLogger
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.ast
import viper.silver.ast.Position
import viper.silver.frontend.DefaultStates
import viper.silver.reporter.NoopReporter

class SymbExLoggerTests extends SilSuite {
  val testDirectories = Seq("symbExLogTests")

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    SymbExLogger.reset()
    SymbExLogger.filePath = files.head
    val fe = new SiliconFrontendWithUnitTesting(files.head)
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
    val configMap = prefixSpecificConfigMap.getOrElse("silicon", Map())
    var args =
      commandLineArguments ++
        Silicon.optionsFromScalaTestConfigMap(configMap)
    args = args ++ Seq("--disableCaching", "--ideModeAdvanced", "--numberOfParallelVerifiers", "1"/*, "--enableMoreCompleteExhale"*/)
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }
}

class SiliconFrontendWithUnitTesting(path: Path) extends SiliconFrontend(NoopReporter) {
  private val originalFilePath: Path = path
  private val fileName: Path = originalFilePath.getFileName()

  /** Is overridden only to append SymbExLogging-UnitTesting-Errors to the Result. **/
  override def result: SilVerificationResult = {
    if(_state < DefaultStates.Verification) super.result
    else{
      val symbExLogUnitTestErrors = verify()
      symbExLogUnitTestErrors match{
        case Nil => super.result
        case s1:Seq[AbstractError] => super.result match{
          case SilSuccess => SilFailure(s1)
          case SilFailure(s2) => SilFailure(s2 ++ s1)
        }
      }
    }
  }

  private def verify(): Seq[SymbExLogUnitTestError] = {
    val expectedPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".elog").toString()
    val actualPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".alog").toString()
    var errorMsg = ""
    var testFailed = false
    val testIsExecuted = Files.exists(Paths.get(expectedPath))

    if (testIsExecuted) {
      val pw = new java.io.PrintWriter(new File(actualPath))
      try pw.write(SymbExLogger.toStructuralTreeString()) finally pw.close()

      val expectedSource = scala.io.Source.fromFile(expectedPath)
      val expected = expectedSource.getLines()

      val actualSource = scala.io.Source.fromFile(actualPath)
      val actual = actualSource.getLines()

      var lineNumber = 0

      while (!testFailed && expected.hasNext && actual.hasNext) {
        if (!actual.next().equals(expected.next())) {
          testFailed = true
        }
        lineNumber = lineNumber + 1
      }
      if (actual.hasNext != expected.hasNext)
        testFailed = true

      if (testFailed) {
        errorMsg = errorMsg + "Unit Test failed, expected output "
        errorMsg = errorMsg + "does not match actual output. "
        errorMsg = errorMsg + "First occurrence at line " + lineNumber + ".\n"
        errorMsg = errorMsg + "Compared Files:\n"
        errorMsg = errorMsg + "expected: " + expectedPath.toString() + "\n"
        errorMsg = errorMsg + "actual:   " + actualPath.toString() + "\n"
      }

      val pathCheckOutput = SymbExLogger.checkPaths()
      if (pathCheckOutput != "") {
        testFailed = true
        errorMsg = errorMsg + "PathChecker: " + pathCheckOutput + "\n"
      }

      actualSource.close()
      expectedSource.close()
    }
    if (testIsExecuted && testFailed) {
      Seq(new SymbExLogUnitTestError(errorMsg))
    }
    else {
      Nil
    }
  }
}

case class SymbExLogUnitTestError(msg: String) extends AbstractError {
  def pos: Position = ast.NoPosition

  def fullId = "symbexlogunittest.error"

  def readableMessage: String = msg
}
