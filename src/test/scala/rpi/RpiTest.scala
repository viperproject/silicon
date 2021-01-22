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
  val testDirectory = "/rpi/tests"

  // run tests
  runTests()

  /**
    * Runs the tests.
    */
  def runTests(): Unit = {
    // get files
    val files = {
      val resource = getClass.getResource(testDirectory)
      val file = new File(resource.getFile)
      Files.listFiles(file)
    }

    // run a test for each file
    files.foreach { file =>
      test(s"testing $file") {
        // create arguments
        val path = file.getPath
        val arguments = Seq(path)
        // run inference on file
        assert(run(arguments))
      }
    }
  }
}
