// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import java.io.FileWriter
import java.nio.file.{Files, Path}

import org.scalatest.DoNotDiscover
import spray.json.{JsArray, JsObject}
import viper.silicon.logger.{SymbExLogger, SymbLog}
import viper.silicon.logger.writer.{SymbExLogReportWriter, TermWriter}
import viper.silicon.{Silicon, SiliconFrontend}
import viper.silicon.state.terms.Term
import viper.silver.reporter.{ExecutionTraceReport, Message, NoopReporter, Reporter}
import viper.silver.testing.{SilSuite, StatisticalTestSuite}
import viper.silver.utility.Paths
import viper.silver.verifier.Verifier

/**
  * This test mechanism is intended for running non-default test suites,
  * in a portable way. Example run command:
  *
  * ```
  * Z3_EXE=z3.exe \
  * BOOGIE_EXE=Boogie.exe \
  * SILICONTESTS_TARGET=./target \
  * SILICONTESTS_WARMUP=./warmup \
  * SILICONTESTS_REPETITIONS=5 \
  * sbt "test:runMain org.scalatest.tools.Runner -o -s viper.silicon.tests.PortableSiliconTests"
  * ```
  *
  * The command above will:
  * 1. Warm-up the JVM by verifying all .vpr files in ./warmup
  * 2. Measure time of 5 runs of each .vpr file in ./target
  * 3. Discard ("trim") the slowest and the fastest runs and compute
  *   - the mean
  *   - the best
  *   - the median
  *   - the worst
  *   run times of all these tests, and
  * 4. Print the timing info (per phase) into STDOUT.
  * 5. Create JAR files (e.g., target/scala-2.12/silicon_2.12-1.1-SNAPSHOT.jar,
  *                            target/scala-2.12/silicon_2.12-1.1-SNAPSHOT-tests.jar)
  *    that can be used to run tests with SBT without the need to distribute/ recompile
  *    the Viper sources. To run the test without recompiling the sources, these
  *    JAR files should be put into a directory test-location/lib/
  *    where test-location/ is the directory where you invoke SBT via:
  *    ```
  *    sbt "set trapExit := false" \
  *    "test:runMain org.scalatest.tools.Runner -o -s viper.silicon.tests.PortableSiliconTests"
  *    ```
  *    Note that this command takes the same environment variables as above.
  *
  * The warmup and the target must be disjoint (not in a sub-directory relation).
  *
  * The default values for environment variables above are:
  *   - SILICONTESTS_TARGET = ???    // This must be set before invoking SBT!
  *   - SILICONTESTS_WARMUP = None   // If not specified, skip JVM warmup phase.
  *   - SILICONTESTS_REPETITIONS = 1 // If less then 3, no "trimming" will happen.
  */
@DoNotDiscover
class PortableSiliconTests extends SilSuite with StatisticalTestSuite {

  val commandLineArguments: Seq[String] = Seq.empty
  private def outputLocationEnvVarName = "SILICONTESTS_OUTPUT"
  private def ouputDirName: Option[String] = Option(System.getenv(outputLocationEnvVarName))
  private def targetDirName: String = Option(System.getenv(targetLocationEnvVarName)).get

  lazy val verifier = {
    var args =
      commandLineArguments ++
        Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    args = args ++ Seq("--disableCaching", "--writeLogFile"/*, "--timeout", "1000"*/, "--numberOfParallelVerifiers", "1"/*, "--enableMoreCompleteExhale"*/)
    val reporter = SymbExReportFileReporter(targetDirName, ouputDirName)
    // val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.SiliconTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    SymbExLogger.reset()
    SymbExLogger.filePath = files.head
    val reporter = verifier match {
      case silicon: Silicon => silicon.reporter
      case _ => NoopReporter
    }
    // val reporter = SymbExReportFileReporter("symbexreport_file_reporter", files.head.getFileName.toString)
    val fe = new SiliconFrontend(reporter)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def name = "Silicon Statistics"
  override def warmupLocationEnvVarName = "SILICONTESTS_WARMUP"
  override def targetLocationEnvVarName = "SILICONTESTS_TARGET"

  override val numOfExecutions: Int = Option(System.getenv("SILICONTESTS_REPETITIONS")) match {
    case Some(reps) =>
      val intReps = reps.toInt
      require(intReps >= 1)
      intReps
    case None => 1
  }
}

case class SymbExReportFileReporter(targetDirName: String, ouputDirName: Option[String], name: String = "symbexreport_file_reporter") extends Reporter {

  def this(targetDirName: String, ouputDirName: Option[String]) = this(targetDirName, ouputDirName, "symbexreport_file_reporter")

  def report(msg: Message): Unit = {
    msg match {
      case ExecutionTraceReport(members: List[SymbLog], axioms: List[Term], functionPostAxioms: List[Term]) => {
        val targetPath = Paths.canonize(targetDirName)
        val isFileInTarget = Paths.isInSubDirectory(targetPath, SymbExLogger.filePath.toFile)
        if (!isFileInTarget) {
          return
        }
        if (ouputDirName.isEmpty) {
          return
        }
        val relativePathInTarget = targetPath.toPath.relativize(SymbExLogger.filePath)
        val outputPath = Paths.canonize(ouputDirName.get).toPath.resolve(relativePathInTarget)
        // replace filename by generated one:
        val reportFilePath = getReportFileName(outputPath)

        val reportObject = JsObject(
          "members" -> SymbExLogReportWriter.toJSON(members),
          "axioms" -> JsArray(axioms.map(TermWriter.toJSON).toVector),
          "functionPostAxioms" -> JsArray(functionPostAxioms.map(TermWriter.toJSON).toVector),
          "macros" -> JsArray(members.flatMap(m => m.macros().map(m => {
            JsObject(
              "macro" -> TermWriter.toJSON(m._1),
              "body" -> TermWriter.toJSON(m._2)
            )
          })).toVector)
        )

        // create directory if it does not exist yet
        reportFilePath.getParent.toFile.mkdirs()
        val reportFile = new FileWriter(reportFilePath.toFile, false)
        reportFile.write(reportObject.prettyPrint)
        reportFile.flush()
      }
      case _ =>
    }
  }

  private def getReportFileName(origPath: Path): Path = {
    val origFileName = origPath.getFileName
    var fileNameSuffix = 1
    while (Files.exists(origPath.resolveSibling(origFileName + "_" + fileNameSuffix.toString + ".json"))) {
      fileNameSuffix = fileNameSuffix + 1
    }
    origPath.resolveSibling(origFileName + "_" + fileNameSuffix.toString + ".json")
  }
}
