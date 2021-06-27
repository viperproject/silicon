package rpi

import org.scalatest.DoNotDiscover
import org.scalatest.funsuite.AnyFunSuite
import rpi.inference.TestRunner
import viper.silver.utility.Paths
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

/**
  * Testing the inference.
  */
@DoNotDiscover
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
    * The path to the tests requiring predicate segments.
    */
  val segmentsDirectory: String = s"$baseDirectory/segments"

  // run tests
  runTests()

  /**
    * Runs the tests.
    */
  def runTests(): Unit = {
    // tests with heuristics
    val heuristicsFiles = getFiles(getPath(heuristicsDirectory))
    heuristicsFiles.foreach { file => runTestWithHeuristics(file) }

    // tests with annotations
    val annotationsFiles = heuristicsFiles ++ getFiles(getPath(annotationsDirectory))
    annotationsFiles.foreach { file => runTestWithAnnotations(file) }

    // tests with segments
    val segmentsFiles = annotationsFiles ++ getFiles(getPath(segmentsDirectory))
    segmentsFiles.foreach { file => runTestWithSegments(file) }
  }

  /**
    * Tests the given file using the inference with heuristics.
    *
    * @param file The path to the file to test.
    */
  def runTestWithHeuristics(file: Path): Unit = {
    val name = s"test with heuristics: $file"
    val arguments = Main.heuristicsOptions :+ file.toString
    runTest(name, arguments)
  }

  /**
    * Tests the given file using the inference with annotations.
    *
    * @param file The path to the file to test.
    */
  def runTestWithAnnotations(file: Path): Unit = {
    val name = s"test with annotations: $file"
    val arguments = Main.annotationsOptions :+ file.toString
    runTest(name, arguments)
  }

  /**
    * Tests the given file using the inference with predicate segments.
    *
    * @param file The path to the file to test.
    */
  def runTestWithSegments(file: Path): Unit = {
    val name = s"test with segments: $file"
    val arguments = Main.segmentsOptions :+ file.toString
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

  private def getPath(path: String): Path = {
    val resource = getClass.getResource(path)
    Paths.pathFromResource(resource)
  }

  private def getFiles(path: Path): Seq[Path] =
    if (Files.isDirectory(path))
      Files
        .newDirectoryStream(path)
        .asScala
        .toSeq
        .flatMap { directory => getFiles(directory) }
        .sortBy { file => file.getFileName.toString }
    else Seq(path)
}
