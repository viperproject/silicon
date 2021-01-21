package rpi

import rpi.inference.Inference
import rpi.util.Parser
import viper.silver.ast

import java.io.File

/**
  * A trait providing useful methods to run the inference.
  */
trait Runner {
  /**
    * Runs the inference with the given arguments.
    *
    * @param arguments The arguments.
    */
  def run(arguments: Seq[String]): Unit = {
    val configuration = new Configuration(arguments)
    run(configuration)
  }

  /**
    * Runs the inference with the given configuration.
    *
    * @param configuration The configuration.
    */
  def run(configuration: Configuration): Unit = {
    // create and start inference
    val inference = new Inference(configuration)
    inference.start()

    // get file(s)
    val files = {
      val path = new File(configuration.path())
      val unfiltered = listFiles(path)
      unfiltered.filter { file => file.getName.endsWith(".vpr") }
    }

    // run inference on all files
    files.foreach { file =>
      // parse file
      val program = Parser.parse(file.getPath)
      // run inference on program
      run(inference, program)
    }

    // stop inference
    inference.stop()
  }

  /**
    * Runs the given inference on the given program.
    *
    * @param inference The inference to run.
    * @param program   The input program.
    * @return The program annotated with the inferred specifications.
    */
  def run(inference: Inference, program: ast.Program): ast.Program =
    inference.run(program)

  /**
    * Lists all files in the folder specified by the given path. If the path points to a file, a list containing that
    * file is returned.
    *
    * @param path The path.
    * @return The sequence of files.
    */
  private def listFiles(path: File): Seq[File] =
    if (path.exists && path.isDirectory)
      path
        .listFiles
        .toSeq
        .flatMap { child => listFiles(child) }
    else Seq(path)
}
