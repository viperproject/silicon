package rpi

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.Paths

import fastparse.core.Parsed.Success
import viper.silver.ast.{And, EqCmp, Exp, FalseLit, Implies, LocalVar, Not, Or, TrueLit}
import viper.silver.verifier.{ModelParser, SingleEntry}

class Smt {
  /**
    * The Z3 process.
    */
  private val process: Process = {
    // check whether z3 file exists and whether it is executable
    val filename = Inference.z3
    val file = Paths.get(filename).toFile
    assert(file.isFile, s"$file is not a file.")
    assert(file.canExecute, s"$file is not executable.")

    // start process
    val builder = new ProcessBuilder(filename, "-in")
    val process = builder.start()

    // add shutdown hook that destroys the process
    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run(): Unit = process.destroy()
    })

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

  def solve(exp: Exp): Map[String, Boolean] = {
    emitCheck(exp)
    readResponse() match {
      case "sat" => readModel()
      case _ => ???
    }
  }

  def emitCheck(exp: Exp): Unit = {
    // enter new scope
    writeLine("(push)")
    // declare variables
    exp
      .collect { case variable: LocalVar => variable.name }.toSet
      .foreach { name: String => writeLine(s"(declare-const $name Bool)") }
    // check
    writeLine(s"(assert ${convert(exp)})")
    writeLine("(check-sat)")
    writeLine("(get-model)")
    // leave scope
    writeLine("(pop)")
  }

  def convert(exp: Exp): String = exp match {
    case TrueLit() => "true"
    case FalseLit() => "false"
    case LocalVar(name, _) => name
    case Not(arg) => s"(not ${convert(arg)})"
    case And(left, right) => s"(and ${convert(left)} ${convert(right)})"
    case Or(left, right) => s"(or ${convert(left)} ${convert(right)})"
    case Implies(left, right) => s"(=> ${convert(left)} ${convert(right)})"
    case EqCmp(left, right) => s"(= ${convert(left)} ${convert(right)})"
    case _ => ???
  }
}
