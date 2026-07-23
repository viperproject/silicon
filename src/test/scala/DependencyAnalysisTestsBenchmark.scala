package viper.silicon.tests

import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyGraphInterpreter, DependencyGraphTestSupporter}
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier

import java.io.PrintWriter

sealed trait BenchmarkMode {
  def name: String
  def isPathSensitive: Boolean
  def extraArgs: Seq[String]
}

object BenchmarkMode {
  case object Default extends BenchmarkMode {
    val name = "DEFAULT"
    val isPathSensitive = false
    val extraArgs = Seq.empty
  }

  case object PathSensitive extends BenchmarkMode {
    val name = "PATH-SENSITIVE"
    val isPathSensitive = true
    val extraArgs = Seq("--enablePathSensitiveDependencyAnalysis")
  }
}

case class FileStats(
                      verifyTimeNs: Long = 0L,
                      queryTimeNs: Long = 0L,
                      precision: Float = 0,
                      graphSize: Int = 0,
                      assumptions: Int = 0,
                      assertions: Int = 0,
                      lowLevelNonInternalAssumptions: Int = 0,
                      lowLevelAllAssumptions: Int = 0,
                      lowLevelNonInternalAssertions: Int = 0,
                      lowLevelAllAssertions: Int = 0,
                      graphInterpreterHash: Int = 0
                    ) {
  def verifyTimeMs: Double = verifyTimeNs.toDouble / 1e6
  def queryTimeMs: Double = queryTimeNs.toDouble / 1e6
}

object BenchmarkCollector {
  private var data = Vector.empty[(String, String, FileStats)]

  def record(file: String, mode: BenchmarkMode, stats: FileStats): Unit = {
    data :+= (file, mode.name, stats)
  }

  def exportResults(path: String): Unit = {
    val writer = new PrintWriter(path)

    try {
      writer.println(
        Seq(
          "file",
          "config",
          "verification time [ms]",
          "query time [ms]",
          "Graph Size",
          "Assumptions",
          "Assertions",
          "low-level Assumptions (non-internal)",
          "low-level Assertions (non-internal)",
          "low-level Assumptions (all)",
          "low-level Assertions (all)",
          "graphInterpreterHash",
          "precision [%]"
        ).mkString(",")
      )

      data.foreach { case (file, config, s) =>
        writer.println(
          Seq(
            file,
            config,
            s.verifyTimeMs,
            s.queryTimeMs,
            s.graphSize,
            s.assumptions,
            s.assertions,
            s.lowLevelNonInternalAssumptions,
            s.lowLevelNonInternalAssertions,
            s.lowLevelAllAssumptions,
            s.lowLevelAllAssertions,
            s.graphInterpreterHash,
            s.precision
          ).mkString(",")
        )
      }
    } finally {
      writer.close()
    }
  }
}

class DependencyAnalysisTestsBenchmark extends AnyFunSuite
  with DependencyAnalysisTestFramework with BeforeAndAfterAll {

  val EXECUTE_TEST = true
  val EXPORT = true
  val ignores: Seq[String] = Seq("iterativeTreeDelete")
  analysisCommandLineArguments = analysisCommandLineArguments ++ Seq("--executeDependencyAnalysisTests")

  // val MODE: BenchmarkMode = BenchmarkMode.Default
  val MODE: BenchmarkMode = BenchmarkMode.PathSensitive

  val testDirectories: Seq[String] = Seq(
    //"dependencyAnalysisTests/all",
    //"dependencyAnalysisTests/unitTests",
    //"dependencyAnalysisTests/real-world-examples"
    "dependencyAnalysisTests/pathsensitivity"
  )

  if (EXECUTE_TEST) {
    testDirectories.foreach { dir =>
      visitFiles(dir, createSingleTest)
    }
  }

  override protected def afterAll(): Unit = {
    if (EXPORT) {
      val suffix =
        if (MODE.isPathSensitive) "path-sensitive"
        else "default"

      BenchmarkCollector.exportResults(
        s"path-sensitivity_benchmark_$suffix.csv"
      )
    }

    super.afterAll()
  }

  private def resetFrontendFor(mode: BenchmarkMode): Unit = {
    frontend.verifier.stop()
    frontend = createFrontend(analysisCommandLineArguments ++ mode.extraArgs)
  }

  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(s"$dirName/$fileName [${MODE.name}]") {
      try {
        resetFrontendFor(MODE)
        executeTest(dirName + "/", fileName, frontend, MODE)
      } catch {
        case t: Throwable => fail(t)
      }
    }
  }

  def executeTest(filePrefix: String, fileName: String, frontend: SilFrontend, mode: BenchmarkMode): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)

    val start = System.nanoTime()
    val result = frontend.verifier.verify(program)

    if (result.isInstanceOf[verifier.Failure]) {
      cancel(s"Program does not verify. Skip test.\n$result")
      return
    }

    val vTime = System.nanoTime() - start

    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter.get :DependencyGraphInterpreter[Final]

    val precision = new DependencyGraphTestSupporter(joinedDependencyGraphInterpreter).testPrecision()
    val allAssumptions = joinedDependencyGraphInterpreter.getNonInternalAssumptionNodes
    val assumptions = UserLevelDependencyAnalysisNode.from(allAssumptions)
    val allAssertions = joinedDependencyGraphInterpreter.getNonInternalAssertionNodes
    val assertions = UserLevelDependencyAnalysisNode.from(allAssertions)
    val nodes = UserLevelDependencyAnalysisNode.from(allAssertions.union(allAssumptions))
    val lowLevelAssumptions = joinedDependencyGraphInterpreter.getAssumptionNodes
    val lowLevelAssertions = joinedDependencyGraphInterpreter.getAssertionNodes
    val qTime = System.nanoTime() - start

    BenchmarkCollector.record(
      filePrefix + "/" + fileName,
      mode,
      FileStats(
        verifyTimeNs = vTime,
        queryTimeNs = qTime,
        precision = precision,
        graphSize = nodes.size,
        assumptions = assumptions.size,
        assertions = assertions.size,
        lowLevelNonInternalAssumptions = allAssumptions.size,
        lowLevelAllAssumptions = lowLevelAssumptions.size,
        lowLevelNonInternalAssertions = allAssertions.size,
        lowLevelAllAssertions = lowLevelAssertions.size,
        graphInterpreterHash = System.identityHashCode(joinedDependencyGraphInterpreter)
      )
    )
  }
}