package rpi

import java.nio.file.{Files, Paths}

import fastparse.core.Parsed
import rpi.learner.Learner
import rpi.teacher.Teacher
import viper.silver.ast._
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}

import scala.io.Source
import scala.util.Properties

object Inference extends Inference {
  /**
    * The flag indicating whether we are on a windows machine.
    */
  lazy val isWindows: Boolean = System
    .getProperty("os.name")
    .toLowerCase
    .startsWith("windows")

  /**
    * The path to the file containing the program to run the inference with.
    */
  lazy val file: String = fileArgument.get

  /**
    * The path to the z3 executable.
    */
  lazy val z3: String = z3Argument
    .orElse(Properties.envOrNone("Z3_EXE"))
    .getOrElse(if (isWindows) "z3.exe" else "z3")

  private var fileArgument: Option[String] = None

  private var z3Argument: Option[String] = None

  /**
    * The entry point of the inference.
    *
    * @param arguments The arguments.
    */
  def main(arguments: Array[String]): Unit = {
    // process arguments
    processArguments(arguments)

    // parse program and run inference
    val program = parse(file).get
    run(program)
  }

  /**
    * Processes the specified arguments. The first argument is expected to be the file containing the program to run the
    * inference with. After that, a sequence of options may follow.
    *
    * @param arguments The arguments.
    */
  private def processArguments(arguments: Seq[String]): Unit = {
    // get file
    assert(1 <= arguments.length, "No file specified.")
    fileArgument = Some(arguments.head)
    // process options
    processOptions(arguments.tail)
  }

  /**
    * Processes the specified options.
    *
    * @param options The options.
    */
  private def processOptions(options: Seq[String]): Unit = options match {
    case "--z3Exe" +: value +: rest =>
      z3Argument = Some(value)
      processOptions(rest)
    case _ +: rest => processOptions(rest)
    case Nil => // do nothing
  }

  def parse(file: String): Option[Program] = {
    // read input
    val path = Paths.get(file)
    val input = Source.fromInputStream(Files.newInputStream(path)).mkString
    // parse program
    val program = FastParser.parse(input, path, None) match {
      case Parsed.Success(program: PProgram, _) =>
        if (program.errors.isEmpty) {
          program.initProperties()
          Some(program)
        } else None
      case Parsed.Failure(_, _, _) => None
    }
    // resolve and translate program
    program
      .flatMap(Resolver(_).run)
      .flatMap(Translator(_).translate)
  }
}

trait Inference {
  def run(program: Program): Unit = {
    val teacher = new Teacher(program)
    val learner = new Learner()

    var hypothesis: Exp = TrueLit()()

    for (i <- 0 until 3) {
      val samples = teacher.check(hypothesis)
      learner.addSamples(samples)
      hypothesis = learner.hypothesis()
      println(hypothesis)
    }
  }
}