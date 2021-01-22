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
    * The path to the tests meant to be executed with heuristics.
    */
  val heuristicsDirectory: String = s"$baseDirectory/heuristics"

  /**
    * The path to the tests meant to be executed with annotations.
    */
  val annotationsDirectory: String = s"$baseDirectory/annotations"

  /**
    * The arguments to the inference runner shared by all tests.
    */
  val baseArguments: Seq[String] = Seq("--usePredicates")

  /**
    * The arguments to the inference with heuristics.
    */
  val heuristicsArguments: Seq[String] = baseArguments ++ Seq("--useHeuristics")

  /**
    * The arguments to the inference with annotations.
    */
  val annotationsArguments: Seq[String] = baseArguments ++ Seq("--useAnnotations")

  // run tests
  runTests()

  /**
    * Runs the tests.
    */
  def runTests(): Unit = {
    // tests with heuristics
    getFiles(heuristicsDirectory)
      .foreach { file => runTestWithHeuristics(file) }

    // tests with annotations
    getFiles(annotationsDirectory)
      .foreach { file => runTestWithAnnotations(file) }
  }

  /**
    * Tests the given file using the inference with heuristics.
    *
    * @param file The file to test.
    */
  def runTestWithHeuristics(file: File): Unit = {
    val name = s"test with heuristics: $file"
    val arguments = heuristicsArguments :+ file.getPath
    runTest(name, arguments)
  }

  /**
    * Tests the given file using the inference with annotations.
    *
    * @param file The file to test.
    */
  def runTestWithAnnotations(file: File): Unit = {
    val name = s"test with annotations: $file"
    val arguments = heuristicsArguments :+ file.getPath
    runTest(name, arguments)
  }

  /**
    * Runs a test with the given name and arguments.
    *
    * @param name      The name of the test.
    * @param arguments The arguments to the inference.
    */
  def runTest(name: String, arguments: Seq[String]): Unit =
    test(name) {
      assert(run(arguments))
    }

  /**
    * Returns all files in the given directory.
    *
    * @param directory The directory.
    * @return The list of files.
    */
  private def getFiles(directory: String): Seq[File] = {
    val resource = getClass.getResource(directory)
    val file = new File(resource.getFile)
    Files.listFiles(file)
  }
}
