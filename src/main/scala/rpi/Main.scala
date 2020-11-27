package rpi

import rpi.inference.Inference
import rpi.util.Parser

import scala.util.Properties

object Main {
  /**
    * Returns the path of the file to be parsed.
    *
    * @return The path.
    */
  def file: String = _file.get

  /**
    * Returns the path to the z3 executable.
    *
    * @return The path to the z3 executable.
    */
  def z3: String = _z3
    .orElse(Properties.envOrNone("Z3_EXE"))
    .getOrElse {
      val isWindows = System.getProperty("os.name").toLowerCase.startsWith("windows")
      if (isWindows) "z3.exe" else "/usr/local/bin/z3" // TODO: z3
    }

  private var _file: Option[String] = None

  private var _z3: Option[String] = None

  /**
    * The entry point of the inference.
    *
    * @param arguments The command line arguments.
    */
  def main(arguments: Array[String]): Unit = {
    // process arguments
    processArguments(arguments)

    // run inference
    val program = Parser.parse(file)

    val inference = new Inference(program)
    inference.start()
    val annotated = inference.annotated()
    inference.stop()

    println(annotated)
  }

  /**
    * Processes the given arguments. The first argument is expected to be the file to be parsed. After that, a sequence
    * of options may follow.
    *
    * @param arguments The arguments to process.
    */
  private def processArguments(arguments: Seq[String]): Unit = {
    // get file
    assert(arguments.nonEmpty, "No file specified.")
    _file = Some(arguments.head)
    // process options
    processOptions(arguments.tail)
  }

  /**
    * Processes the given sequence of options.
    *
    * @param options The options to process.
    */
  private def processOptions(options: Seq[String]): Unit = options match {
    case "-z3" +: value +: rest => _z3 = Some(value); processOptions(rest)
    case _ +: rest => processOptions(rest) // ignore unknown option
    case Nil => // we are done
  }
}
