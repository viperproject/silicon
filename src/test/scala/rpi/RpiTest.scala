package rpi

import rpi.inference.Inference
import java.io.File

import org.scalatest.FunSuite
import rpi.util.Parser
import viper.silver.verifier.{Failure, Success}

class RpiTest extends FunSuite {
  /**
    * The file to test. If the path points to a directory, all files within this directory are tested.
    */
  val path = "/rpi/tests/recursion.vpr"

  /**
    * Run all tests.
    */
  run()

  /**
    * Runs all tests.
    */
  def run(): Unit = {
    // the files to test
    val files = {
      val resource = getClass.getResource(path)
      val file = new File(resource.getFile)
      getFiles(file).filter { file => file.getName.endsWith(".vpr") }
    }

    // run tests one by one
    files.foreach { file =>
      test(s"testing: ${file.getName}") {
        // parses the program
        val path = file.getPath
        val program = Parser.parse(path)

        // start inference
        val inference = new Inference(program)
        inference.start()

        // infer specifications
        val annotated = inference.annotated()
        println(annotated)

        // check specifications
        val result = inference.verify(annotated)
        result match {
          case Success => // do nothing
          case Failure(errors) =>
            // fail
            assert(false)
        }

        // stop inference
        inference.stop()
      }
    }
  }

  private def getFiles(path: File): Seq[File] =
    if (path.exists && path.isDirectory)
      path
        .listFiles()
        .toSeq
        .flatMap { nested => getFiles(nested) }
    else Seq(path)
}
