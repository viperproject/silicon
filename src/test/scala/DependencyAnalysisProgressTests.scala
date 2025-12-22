import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis.DependencyAnalysisReporter
import viper.silicon.tests.DependencyAnalysisTestFramework
import viper.silver.ast.Program
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.{Failure, VerificationResult}

import java.nio.file.{Files, Path, Paths}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`

class DependencyAnalysisProgressTests extends AnyFunSuite with DependencyAnalysisTestFramework {

  val ignores: Seq[String] = Seq.empty
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/verificationProgress/incrRand"
  )

  testDirectories foreach (dir => createSingleTest(dir, ""))

  def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName) {
      try{
        val directoryStream = Files.newDirectoryStream(Paths.get(getClass.getClassLoader.getResource(dirName).toURI))
        val dirContent = directoryStream.toList

        for (filePath: Path <- dirContent.sorted
             if Files.isReadable(filePath)) {
          val rawFileName = filePath.getFileName.toString
          if (rawFileName.endsWith(".vpr")) {
            val vprFileName = rawFileName.replace(".vpr", "")
            if (!ignores.contains(vprFileName))
              resetFrontend()
              executeTest(dirName + "/", vprFileName, frontend)
          }
        }
      }catch{
        case t: Throwable => fail(t.toString)
      }
    }
  }


  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result: VerificationResult = frontend.verifier.verify(program)
    val errors = result match {
      case failure: Failure => failure.errors
      case _ => List.empty
    }

    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter

    val (progressA, progressB, info) = joinedDependencyGraphInterpreter.get.computeVerificationProgress()

    println(s"$filePrefix$fileName:\n\tProgress A = $progressA\t\t\tProgress P = $progressB")
    println(info)
  }
}
