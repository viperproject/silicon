package viper.silicon.tests

import viper.silicon.dependencyAnalysis.DependencyAnalysisReporter
import viper.silver.ast.Program
import viper.silver.frontend.SilFrontend
import viper.silver.verifier
import viper.silver.verifier.VerificationResult

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.collection.convert.ImplicitConversions.`iterable AsScalaIterable`


object VerificationProgressRunner extends DependencyAnalysisTestFramework {

  val ignores: Seq[String] = Seq.empty
  val pathToTests: String = "src/test/resources/"
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/verificationProgress/incrRand",
    "dependencyAnalysisTests/verificationProgress/perms"
  )

  def main(args: Array[String]): Unit = {
    testDirectories foreach computeProgressForDir
  }

  def computeProgressForDir(dirName: String): Unit = {
    val writer = new PrintWriter(pathToTests + dirName + "/results_" + System.currentTimeMillis() + ".csv")

    val directoryStream = Files.newDirectoryStream(Paths.get(pathToTests, dirName))
    val dirContent = directoryStream.toList
    writer.println("File name\tProgress (Peter)\tProgress (Lea)\tverification successful?")
    println(s"\n$dirName")
    println("File name\tProgress (Peter)\tProgress (Lea)\tverification successful?")

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)) {
      val rawFileName = filePath.getFileName.toString
      if (rawFileName.endsWith(".vpr")) {
        val vprFileName = rawFileName.replace(".vpr", "")
        if (!ignores.contains(vprFileName))
          resetFrontend()
        computeProgress(dirName + "/", vprFileName, frontend, writer)
      }
    }
    writer.close()
  }


  def computeProgress(filePrefix: String,
                      fileName: String,
                      frontend: SilFrontend,
                      writer: PrintWriter): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result: VerificationResult = frontend.verifier.verify(program)

    val hasFailures = result.isInstanceOf[verifier.Failure]

    val joinedDependencyGraphInterpreter = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].joinedDependencyGraphInterpreter

    val (progressPeter, progressLea, _) = joinedDependencyGraphInterpreter.get.computeVerificationProgress()

    writer.println(f"$fileName\t$progressPeter%.3f\t$progressLea%.3f\t${!hasFailures}")
    println(f"$fileName\t$progressPeter%.3f\t$progressLea%.3f\t${!hasFailures}")
  }
}
