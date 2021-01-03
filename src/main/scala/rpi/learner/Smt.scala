package rpi.learner

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.Paths

import fastparse.core.Parsed.Success
import rpi.Main
import viper.silver.{ast => sil}
import viper.silver.verifier.{ModelParser, SingleEntry}

class Smt {
  /**
    * The z3 process.
    */
  private val process: Process = {
    // check whether the z3 file exists and whether it is executable.
    val filename = Main.z3
    val file = Paths.get(filename).toFile
    assert(file.isFile, s"$file is not a file.")
    assert(file.canExecute, s"$file is not executable.")

    // start process
    val builder = new ProcessBuilder(filename, "-in")
    val process = builder.start()

    // add shutdown hook that destroys the process
    val thread = new Thread {
      override def run(): Unit = process.destroy()
    }
    Runtime.getRuntime.addShutdownHook(thread)

    // return process
    process
  }

  /**
    * The reader used to read from Z3's output.
    */
  private lazy val reader = {
    val inputStream = process.getInputStream
    val inputStreamReader = new InputStreamReader(inputStream)
    new BufferedReader(inputStreamReader)
  }

  /**
    * The writer used to write to Z3's input.
    */
  private val writer = {
    val outputStream = process.getOutputStream
    val outputStreamWriter = new OutputStreamWriter(outputStream)
    val bufferedWriter = new BufferedWriter(outputStreamWriter)
    new PrintWriter(bufferedWriter, true)
  }

  /**
    * Writes the specified line to Z3's input.
    *
    * @param line The input line.
    */
  def writeLine(line: String): Unit = {
    println(line)
    writer.println(line)
  }

  /**
    * Initializes Z3.
    */
  def initialize(): Unit = {
    // disable automatic self configuration
    writeLine("(set-option :auto-config false)")
    // pick random seed to make things deterministic
    writeLine("(set-option :random-seed 0)")
    // set model format
    writeLine("(set-option :model.v2 true)")
    // allow partial models
    // TODO: Does change do anything?
    writeLine("(set-option :model.completion false)")
  }

  /**
    * Reads a line from Z3's output.
    *
    * @return The output line.
    */
  def readLine(): String = reader.readLine()

  /**
    * Reads a response from Z3's output.
    *
    * @return The response.
    */
  def readResponse(): String = {
    var response = readLine()
    while (response.count(_ == '(') != response.count(_ == ')')) {
      response ++= "\n" ++ readLine()
    }
    response
  }

  def readModel(): Map[String, Boolean] = {
    // read response
    var response = readLine()
    while (!response.endsWith("\"")) {
      response ++= "\n" ++ readLine()
    }
    response = response.replace("\"", "")
    // parse response and create model
    ModelParser.model.parse(response) match {
      case Success(model, _) => model.entries.mapValues {
        case SingleEntry("true") => true
        case SingleEntry("false") => false
      }
    }
  }

  def solve(constraints: Seq[sil.Exp]): Map[String, Boolean] = {
    emitCheck(constraints)
    readResponse() match {
      case "sat" => readModel()
      case response =>
        println(s"unexpected response: $response")
        ???
    }
  }

  def emitCheck(constraints: Seq[sil.Exp]): Unit = {
    // enter new scope
    writeLine("(push)")
    // declare variables
    constraints
      .flatMap { constraint =>
        constraint.collect { case variable: sil.LocalVar => variable.name }
      }
      .distinct
      .foreach { name: String => writeLine(s"(declare-const $name Bool)") }
    // check
    constraints
      .foreach { constraint =>
        writeLine(s"(assert ${convert(constraint)})")
      }
    writeLine("(check-sat)")
    writeLine("(get-model)")
    // leave scope
    writeLine("(pop)")
  }

  def convert(exp: sil.Exp): String = exp match {
    case sil.TrueLit() => "true"
    case sil.FalseLit() => "false"
    case sil.LocalVar(name, _) => name
    case sil.Not(arg) => s"(not ${convert(arg)})"
    case sil.And(left, right) => s"(and ${convert(left)} ${convert(right)})"
    case sil.Or(left, right) => s"(or ${convert(left)} ${convert(right)})"
    case sil.Implies(left, right) => s"(=> ${convert(left)} ${convert(right)})"
    case sil.EqCmp(left, right) => s"(= ${convert(left)} ${convert(right)})"
    case _ => ???
  }
}