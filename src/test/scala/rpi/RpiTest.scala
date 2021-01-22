package rpi

import org.scalatest.funsuite.AnyFunSuite
import rpi.util.Files

import java.io.File

/**
  * Testing the inference.
  */
class RpiTest extends AnyFunSuite with TestRunner {

  /**
    * The path to the tests.
    */
  val baseDirectory: String = "/rpi/tests"

  /**
    * The path to the test meant to be executed using heuristics.
    */
  val heuristicsDirectory: String = s"$baseDirectory/heuristics"

  /**
    * The arguments to the inference runner shared by all tests.
    */
  val baseArguments: Seq[String] = Seq.empty

  /**
    * The arguments to the inference runner for the test meant to be executed using heuristics.
    */
  val heuristicsArguments: Seq[String] = baseArguments ++ Seq("--useHeuristics")

  // run tests
  runTests()

  /**
    * Runs the tests.
    */
  def runTests(): Unit = {
    // heuristics tests
    val heuristicsFiles = getFiles(heuristicsDirectory)
    heuristicsFiles.foreach { file => runHeuristicsTest(file) }
  }

  /**
    * Tests the given file using the inference with heuristics.
    *
    * @param file The file to test.
    */
  def runHeuristicsTest(file: File): Unit = {
    val name = s"test using heuristics: $file"
    test(name) {
      // create arguments
      val path = file.getPath
      val arguments = heuristicsArguments :+ path
      // run inference on file
      assert(run(arguments))
    }
  }

  private def getFiles(directory: String) = {
    val resource = getClass.getResource(directory)
    val file = new File(resource.getFile)
    Files.listFiles(file)
  }
}
