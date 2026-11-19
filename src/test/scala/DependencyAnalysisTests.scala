// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphTestSupporter
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier

class DependencyAnalysisTests extends AnyFunSuite with DependencyAnalysisTestFramework {

  val EXECUTE_TEST = true
  override val EXPORT_PRUNED_PROGRAMS: Boolean = false
  val ignores: Seq[String] = Seq()
  val depAnalysisModeArg = Seq("--dependencyAnalysis=computeGraphOnly")

  analysisCommandLineArguments = analysisCommandLineArguments ++ depAnalysisModeArg
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/real-world-examples",
    "dependencyAnalysisTests/verificationProgressTests",
    "dependencyAnalysisTests/guidance",
  )

  if (EXECUTE_TEST) {
    testDirectories foreach (dir => visitFiles(dir, createSingleTest))
    // TODO ake: more complete exhale tests
//    analysisCommandLineArguments = Seq("--enableMoreCompleteExhale") ++ analysisCommandLineArguments
//    visitFiles("dependencyAnalysisTests/mce", createSingleTest)
  }

  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName + "/" + fileName) {
      try{
        resetFrontend()
        executeTest(dirName + "/", fileName, frontend)
      }catch{
        case t: Throwable => fail(t.getMessage, t)
      }
    }
  }

  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend): Unit = {
    println(s"$filePrefix$fileName")

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)
    if (result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val fullGraphQueries = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].finalGraphQueries.get

    val testSupporter = new DependencyGraphTestSupporter(fullGraphQueries)
    testSupporter.testDependencies()
    testSupporter.testNodeTypes()
    new PruningTest(filePrefix + "/" + fileName, program, fullGraphQueries).execute()

    if (filePrefix.contains("verificationProgressTests")) {
      new VerificationProgressTest(filePrefix + "/" + fileName, fullGraphQueries).execute()
    } else if (filePrefix.contains("guidance")) {
      new GuidanceTest(program, fullGraphQueries).execute()
    }
  }
}
