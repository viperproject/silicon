package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.assumptionAnalysis._
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier

import java.io.{File, PrintWriter}
import java.time._
import java.time.format.DateTimeFormatter
import scala.annotation.unused


class AssumptionAnalysisTests extends AnyFunSuite with AssumptionAnalysisTestFramework {

  val CHECK_PRECISION = false
  val EXECUTE_TEST = true
  val EXECUTE_PERFORMANCE_BENCHMARK = false
  val ignores: Seq[String] = Seq("example1", "example2", "iterativeTreeDelete", "listAppend_wands")
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/unitTests",
    "dependencyAnalysisTests/real-world-examples",
//    "frontends/gobra",
//    "symbExLogTests",
//    "dependencyAnalysisTests/quick"
//    "dependencyAnalysisTests/fromSilver",
//    "dependencyAnalysisTests/performanceBenchmark"
//    "dependencyAnalysisTests/precisionTests/quantifiedPermissions"
//    "andrea/debug"
  )


  if(EXECUTE_PERFORMANCE_BENCHMARK)
    test("performance benchmark") {
      val basePath = "src/test/resources/dependencyAnalysisTests/performanceBenchmark"
      val directory = new File(basePath)
      directory.mkdir()
      val now: LocalDateTime = LocalDateTime.now()
      val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")
      val writer = new PrintWriter(s"$basePath/result_${now.format(formatter)}.out")
      val proofCoverageWriter = new PrintWriter(s"$basePath/proofCoverage_${now.format(formatter)}.out")
      writer.println(f"test name,baseline (ms),analysis (ms),analysis/baseline,program size")
      testDirectories foreach (dir => visitFiles(dir, executePerformanceBenchmark(_, _, writer, proofCoverageWriter)))
      writer.close()
      proofCoverageWriter.close()
    }

//  createSingleTest("dependencyAnalysisTests/real-world-examples", "listAppend")

  if(EXECUTE_TEST) {
    testDirectories foreach (dir => visitFiles(dir, createSingleTest))
//    analysisCommandLineArguments = Seq("--enableMoreCompleteExhale") ++ analysisCommandLineArguments
//    visitFiles("dependencyAnalysisTests/mce", createSingleTest)
  }




  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName + "/" + fileName) {
      try{
        resetFrontend()
        executeTest(dirName + "/", fileName, frontend)
      }catch{
        case t: Throwable => fail(t.getMessage)
      }
    }
  }


  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val assumptionAnalysisInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpretersPerMember
    val joinedAssumptionAnalysisInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedAssumptionAnalysisInterpreter

    AnnotatedTest(program, assumptionAnalysisInterpreters, CHECK_PRECISION).execute()
    PruningTest(filePrefix + "/" + fileName, program, joinedAssumptionAnalysisInterpreter.get).execute()
  }

  def executePerformanceBenchmark(filePrefix: String,
                                fileName: String,
                                writer: PrintWriter,
                                proofCoverageWriter: PrintWriter): Unit = {
    if(fileName.endsWith("_naive")) return

    val program: Program = tests.loadProgram(filePrefix + "/", fileName, frontend)
    val naiveProgram: Option[Program] = try{
      Some(tests.loadProgram(filePrefix + "/", fileName + "_naive", frontend))
    }catch{
      case _: Throwable => None
    }

    val frontend_ = createFrontend(analysisCommandLineArguments)
    val result = frontend_.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val assumptionAnalysisInterpreters = frontend_.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpretersPerMember

    proofCoverageWriter.println(filePrefix + "/" + fileName)
    assumptionAnalysisInterpreters foreach (memberInterpreter => {
      memberInterpreter.getExplicitAssertionNodes.groupBy(_.sourceInfo.getTopLevelSource) foreach {case (source, nodes) =>
          proofCoverageWriter.println(memberInterpreter.getName + " " + source.toString.replace("\n", " ") + " ---> " + memberInterpreter.computeProofCoverage(nodes)._1)}
      proofCoverageWriter.println("overall " + memberInterpreter.getName + " ---> + " + memberInterpreter.computeProofCoverage()._1)
    })
    proofCoverageWriter.println()

    new PerformanceBenchmark(filePrefix + "/" + fileName, program, naiveProgram, writer, program.toString().split("\n").length).execute()
  }


  class PerformanceBenchmark(name: String, program: Program, @unused naiveProgram: Option[Program], writer: PrintWriter, programSize: Int) {

    private def printResult(str: String): Unit = {
      writer.print(str)
      print(str)
    }

    def execute(): Unit = {
      printResult(f"$name,")

      val analysisDurationMs: Double = verifyAndMeasure(program, analysisCommandLineArguments)
      val baselineDurationMs: Double = verifyAndMeasure(program, baseCommandLineArguments)

      printResult(f"$baselineDurationMs,$analysisDurationMs,${analysisDurationMs/baselineDurationMs},$programSize\n")
    }

    private def verifyAndMeasure(program_ : Program, commandLineArgs: Seq[String]) = {
      val NUM_RUNS = 5
      val frontend_ = createFrontend(commandLineArgs)
      try {
        val startAnalysis = System.nanoTime()
        for (i <- 0 until NUM_RUNS) {
          val result = frontend_.verifier.verify(program_)
          if(result.isInstanceOf[verifier.Failure]) {
            println(f"$i ${result.toString}")
            throw new Exception(f"Failed $result")
          }
        }
        val endAnalysis = System.nanoTime()
        val analysisDurationMs = (endAnalysis - startAnalysis) / 1e6 / NUM_RUNS
        analysisDurationMs
      }catch{
        case t: Throwable =>
          println(t)
          Double.NaN
      }
    }
  }
}


