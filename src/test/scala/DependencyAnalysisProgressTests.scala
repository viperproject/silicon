package viper.silicon.tests

import org.scalatest.DoNotDiscover
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.dependencyAnalysis.DependencyAnalysisReporter
import viper.silver.ast.Program
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.{Failure, VerificationResult}

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`

@DoNotDiscover
class DependencyAnalysisProgressTests extends AnyFunSuite with DependencyAnalysisTestFramework {

  val ignores: Seq[String] = Seq.empty
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/verificationProgress/incrRand"
  )

  testDirectories foreach (dir => createSingleTest(dir, ""))

  def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName) {
      val writer = new PrintWriter("src/test/resources/" + dirName + "/results_" + System.currentTimeMillis() + ".csv")
      try{
        val dirPath = Paths.get(getClass.getClassLoader.getResource(dirName).toURI)
        val directoryStream = Files.newDirectoryStream(dirPath)
        val dirContent = directoryStream.toList
        writer.println("File name,Progress (Peter),Progress (Lea)")

        for (filePath: Path <- dirContent.sorted
             if Files.isReadable(filePath)) {
          val rawFileName = filePath.getFileName.toString
          if (rawFileName.endsWith(".vpr")) {
            val vprFileName = rawFileName.replace(".vpr", "")
            if (!ignores.contains(vprFileName))
              resetFrontend()
              executeTest(dirName + "/", vprFileName, frontend, writer)
          }
        }
        writer.close()
      }catch{
        case t: Throwable => fail(t.toString)
      }
    }
  }


  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend,
                  writer: PrintWriter): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result: VerificationResult = frontend.verifier.verify(program)
    val errors = result match {
      case failure: Failure => failure.errors
      case _ => List.empty
    }

    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter

    val (progressPeter, progressLea, _) = joinedDependencyGraphInterpreter.get.computeVerificationProgress()

    println(s"$filePrefix$fileName:\n\tProgress (Peter) = $progressPeter\t\t\tProgress (Lea) = $progressLea\n")
    writer.println(s"$fileName,\t$progressPeter,\t$progressLea")
  }
}
