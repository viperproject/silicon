package rpi

import java.nio.file.{Files, Paths}

import fastparse.core.Parsed.Success
import viper.silver.ast.{Exp, Program, TrueLit, While}
import viper.silver.parser.{FastParser, PProgram, Resolver, Translator}

import scala.io.Source
import scala.util.Properties


object Inference {
  /**
    * Returns he file to be parsed.
    *
    * @return The file to be parsed.
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
      if (isWindows) "z3.exe" else "z3"
    }

  /**
    * The file to be parsed.
    */
  private var _file: Option[String] = None

  /**
    * The path to the z3 executable.
    */
  private var _z3: Option[String] = None

  /**
    * The entry point of the inference.
    *
    * @param args The command line arguments.
    */
  def main(args: Array[String]): Unit = {
    // process arguments
    processArgs(args)

    // run inference
    val program = parse(file).get
    val inference = new Inference(program)
    inference.start()
    inference.run()
    inference.stop()
  }

  /**
    * Process the given arguments. The first argument is expected to be the file to be parsed. After that a sequence of
    * of options may follow.
    *
    * @param args The arguments.
    */
  private def processArgs(args: Seq[String]): Unit = {
    // get file
    assert(args.nonEmpty, "no file specified.")
    _file = Some(args.head)
    // process options
    processOptions(args.tail)
  }

  /**
    * Processes the sequence of options represented by the given arguments.
    *
    * @param args The arguments.
    */
  private def processOptions(args: Seq[String]): Unit = args match {
    case "-z3" +: value +: rest => _z3 = Some(value); processOptions(rest)
    case _ +: rest => processOptions(rest) // ignore unknown option
    case Nil => // we are done
  }

  /**
    * Parses the given file.
    *
    * @param file The file to parse.
    * @return The parsed program.
    */
  private def parse(file: String): Option[Program] = {
    // read input
    val path = Paths.get(file)
    val input = Source.fromInputStream(Files.newInputStream(path)).mkString
    // parse program
    val program = FastParser.parse(input, path, None) match {
      case Success(program: PProgram, _) if program.errors.isEmpty =>
        program.initProperties()
        Some(program)
      case _ => None
    }
    // resolve and translate program
    program
      .flatMap(Resolver(_).run)
      .flatMap(Translator(_).translate)
  }
}

class Inference(val program: Program) {
  /**
    * The teacher providing the examples.
    */
  private val teacher: Teacher = new Teacher(this)

  /**
    * The learner used synthesizing hypotheses.
    */
  private val learner: Learner = new Learner(this)

  /**
    * The sequence of atomic predicates.
    */
  lazy val atoms: Seq[Exp] = program
    .deepCollect { case While(cond, _, _) => cond }
    .distinct

  /**
    * The loops appearing within the program.
    *
    * TODO: Replace with triples {pre} s {post} or something alike.
    */
  lazy val loops: Seq[While] = program.deepCollect { case loop: While => loop }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    teacher.start()
    learner.start()
  }

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    teacher.stop()
    learner.stop()
  }

  def run(): Unit = {
    var hypothesis: Exp = TrueLit()()

    for (i <- 0 until 3) {
      val examples = teacher.check(hypothesis)
      learner.addExamples(examples)
      hypothesis = learner.hypothesis()
      println(hypothesis)
    }
  }
}

