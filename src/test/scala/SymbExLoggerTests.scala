// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import viper.silicon.logger.SymbExLog
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silver.ast
import viper.silver.ast.Position
import viper.silver.frontend.{DefaultStates, Frontend}
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.{AbstractError, Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}

import java.io.File
import java.nio.file.{Files, Path, Paths}

class SymbExLoggerTests extends SilSuite {
  val testDirectories = Seq("symbExLogTests")

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    val fe = new SiliconFrontendWithUnitTesting(files.head)
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
    val debugInfo = ("startedBy" -> "viper.silicon.SymbExLoggerTests") :: Nil
    new Silicon(reporter, debugInfo)
  }

  lazy val verifiers = List(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    silicon.parseCommandLine(args ++ commandLineArguments :+ Silicon.dummyInputFilename)
  }

  val commandLineArguments: Seq[String] =
    Seq(
      "--timeout", "300" /* seconds */,
      "--disableCaching", "--ideModeAdvanced",
      "--numberOfParallelVerifiers", "1")
}

class SiliconFrontendWithUnitTesting(path: Path) extends SiliconFrontend(NoopReporter) {
  private val originalFilePath: Path = path
  private val fileName: Path = originalFilePath.getFileName

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
    val expectedPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".elog").toString
    val actualPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".alog").toString
    val testIsExecuted = Files.exists(Paths.get(expectedPath))

    if (testIsExecuted) {
      val pw = new java.io.PrintWriter(new File(actualPath))
      try pw.write(siliconInstance.symbExLog.asInstanceOf[SymbExLog].toSimpleTreeString) finally pw.close()

      val expectedSource = scala.io.Source.fromFile(expectedPath)
      val expected = expectedSource.getLines()

      val actualSource = scala.io.Source.fromFile(actualPath)
      val actual = actualSource.getLines()

      val comparisonResult = compare(expected, actual)

      actualSource.close()
      expectedSource.close()

      comparisonResult match {
        case cf: ComparisonFailed =>
          val errorMsg = s"Unit Test failed, expected output " +
            s"does not match actual output. First occurrence at line ${cf.lineNumber}.\n" +
            s"Compared Files:\n" +
            s"expected: $expectedPath\n" +
            s"actual:   $actualPath\n"
          Seq(SymbExLogUnitTestError(errorMsg))
        case _ => Nil
      }
    } else {
      Nil
    }
  }

  private def compare(expected: Iterator[String], actual: Iterator[String]): ComparisonResult = {
    var currentExpected: String = null
    var lineNumber = 0
    while((currentExpected != null || expected.hasNext) && actual.hasNext) {
      if (currentExpected == null) {
        currentExpected = expected.next()
        lineNumber = lineNumber + 1
      }
      val currentActual = actual.next()
      val currentExpectedIndentationLength = getIndentationLength(currentExpected)
      val currentActualIndentationLength = getIndentationLength(currentActual)
      val currentExpectedStripped = currentExpected.substring(currentExpectedIndentationLength)
      val currentActualStripped = currentActual.substring(currentActualIndentationLength)

      // condition that currentExpectedStripped and currentActualStripped match:
      // 1. the stripped versions are equal
      // 2. currentActualIndentationLength >= currentExpectedIndentationLength
      // notes:
      // 2.: actual is expected to have the same content or more. Therefore, more scopes and hence
      //      more indentation can occur.
      // a check comparing the indentation difference to the last matched line is not possible:
      // expected:
      //          comment: Reachable
      //  Join
      // actual:
      // comment: Reachable
      //                decider assume !(b2@3@01 && b1@2@01)
      //                evaluate 5
      //    decider assume a@6@01 == (b1@2@01 ? (b2@3@01 ? 2 : 3) : (b2@3@01 && b1@2@01 ? dead_then@5@01 : 5))
      //  execute a := 1 + (b1 ? 1 : 2) + 2
      //    evaluate 1 + (b1 ? 1 : 2) + 2
      //      evaluate 1 + (b1 ? 1 : 2)
      //        evaluate 1
      //        evaluate (b1 ? 1 : 2)
      //          conditional expression (b1 ? 1 : 2)
      //            evaluate b1
      //          Join
      // the indentation reduction can be larger (i.e. more negative) for actual, because more scopes might be undone.
      // similary for indentation growth: actual might contain more scopes, hence more indentation is added.
      // however, just considering the absolute value does not work either: in the above example,
      // a mix of decrease and increase happens. The amount of indentation increase is arbitrary and depends on the
      // scopes in actual (and cannot be inferred from expected). E.g. "Join" could either be more to the
      // left (i.e. less indentation) or more the the right (i.e. more indentation)
      // val expectedIndentationLengthDiff = currentExpectedIndentationLength - lastMatchedExpectedIndentationLength
      // val actualIndentationLengthDiff = currentActualIndentationLength - lastMatchedActualIndentationLength
      // Math.abs(actualIndentationLengthDiff) >= Math.abs(expectedIndentationLengthDiff) therefore does not work
      if (currentExpectedStripped.equals(currentActualStripped)
        && currentActualIndentationLength >= currentExpectedIndentationLength) {
        // set currentExpected to null such that the next line is used in the next iteration
        currentExpected = null
      }
    }
    if (expected.hasNext) {
      ComparisonFailed(lineNumber) // the current line could not be matched
    } else {
      ComparisonSuccessful()
    }
  }

  private def getIndentationLength(s: String): Int = s.segmentLength(c => c == ' ')
}

case class SymbExLogUnitTestError(msg: String) extends AbstractError {
  val pos: Position = ast.NoPosition

  val fullId = "symbexlogunittest.error"

  val readableMessage: String = msg
}

case class ComparisonFailed(lineNumber: Int) extends ComparisonResult
case class ComparisonSuccessful() extends ComparisonResult
trait ComparisonResult
