// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.cliTool.DependencyGraphImporter
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyGraphInterpreter, DependencyGraphTestSupporter}
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier


class DependencyAnalysisTests extends AnyFunSuite with DependencyAnalysisTestFramework {

  val EXECUTE_TEST = true
  val TEST_IMPORTER = false // if true, the tests are executed on the graph that got exported and then imported via the GraphImporter
  override val EXPORT_PRUNED_PROGRAMS: Boolean = false
  val ignores: Seq[String] = Seq()
  val depAnalysisModeArg = if(TEST_IMPORTER) Seq("--dependencyAnalysisMode=export>testExports") else Seq()
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

    val name = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter.map(_.getName).getOrElse("graph")

    val fullGraphInterpreter = if (TEST_IMPORTER) {
      println("--------\nTesting via the graph importer.")
      val importedGraph = DependencyGraphImporter.importGraphFromCsv(s"testExports")
      new DependencyGraphInterpreter[Final](name, importedGraph, List.empty, None)
    } else {
      frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter.get
    }

    val testSupporter = new DependencyGraphTestSupporter(fullGraphInterpreter)
    testSupporter.testDependencies()
    testSupporter.testNodeTypes()
    new PruningTest(filePrefix + "/" + fileName, program, fullGraphInterpreter).execute()

    if (filePrefix.contains("verificationProgressTests")) {
      new VerificationProgressTest(filePrefix + "/" + fileName, fullGraphInterpreter).execute()
    } else if (filePrefix.contains("guidance")) {
      new GuidanceTest(program, fullGraphInterpreter).execute()
    }
  }
}
