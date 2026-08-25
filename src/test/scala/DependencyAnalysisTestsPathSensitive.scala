package viper.silicon.tests

import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis._
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphTestSupporter

class DependencyAnalysisTestsPathSensitive extends AnyFunSuite with DependencyAnalysisTestFramework with BeforeAndAfterAll {

  val EXECUTE_TEST = true
  val CHECK_PRECISION = false
  val ignores: Seq[String] = Seq("iterativeTreeDelete")
  analysisCommandLineArguments = analysisCommandLineArguments ++ Seq("--executeDependencyAnalysisTests") ++ Seq("--enablePathSensitiveDependencyAnalysis")
	val testDirectories: Seq[String] = Seq(
    //"dependencyAnalysisTests/all",
    //"dependencyAnalysisTests/unitTests",
    //"dependencyAnalysisTests/real-world-examples",
    "dependencyAnalysisTests/pathsensitivity"
  )

  if(EXECUTE_TEST) {
    testDirectories.foreach { dir =>
      visitFiles(dir, (d, f) => {
        createSingleTest(d, f)
      })
    }
  }

  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName + "/" + fileName ) {
      try{
        resetFrontend()
        executeTest(dirName + "/", fileName, frontend)
      }catch{
        case t: Throwable => fail(t)
      }
    }
  }

  def executeTest(filePrefix: String, fileName: String, frontend: SilFrontend): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)

    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter.get

    new DependencyGraphTestSupporter(joinedDependencyGraphInterpreter).testDependencies(CHECK_PRECISION)
    // new PruningTest(filePrefix + "/" + fileName, program, joinedDependencyGraphInterpreter).execute()
  }
}
