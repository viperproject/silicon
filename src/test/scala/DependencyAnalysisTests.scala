package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis._
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier


class DependencyAnalysisTests extends AnyFunSuite with DependencyAnalysisTestFramework {

  val CHECK_PRECISION = false
  val EXECUTE_TEST = true
  override val EXPORT_PRUNED_PROGRAMS: Boolean = false
  val ignores: Seq[String] = Seq()
	analysisCommandLineArguments = analysisCommandLineArguments ++ Seq("--executeDependencyAnalysisTests")
	val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/unitTests",
    "dependencyAnalysisTests/real-world-examples",
  )

  if(EXECUTE_TEST) {
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
        case t: Throwable => fail(t)
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

    val dependencyGraphInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].dependencyGraphInterpretersPerMember
    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter

		// TODO ake: annotated tests can be removed once all tests are migrated to the new test annotations (TestSupporter)
    new AnnotatedTest(program, dependencyGraphInterpreters, CHECK_PRECISION).execute()
    new PruningTest(filePrefix + "/" + fileName, program, joinedDependencyGraphInterpreter.get).execute()
  }
}
