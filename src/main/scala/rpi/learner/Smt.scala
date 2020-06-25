package rpi.learner

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.Paths

import rpi.Inference

class Smt {
  /**
    * The Z3 process.
    */
  private lazy val process: Process = {
    // check whether file exists and is executable
    val filename = Inference.z3
    val file = Paths.get(filename).toFile
    assert(file.isFile, s"$file is not a file.")
    assert(file.canExecute, s"$file is not executable")

    // start process
    val processBuilder = new ProcessBuilder(filename, "-in") // TODO: Is this correct ?
    val process = processBuilder.start()

    // add shutdown hook
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
  def writeLine(line: String): Unit = writer.println(line)

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

  /**
    * Initializes Z3.
    */
  def initialize(): Unit = {
    // disable automatic self configuration
    writeLine("(set-option :auto-config false)")
    // pick random seed to make things deterministic
    writeLine("(set-option :random-seed 0)")
  }

  def checkSat(): Boolean = readResponse() match {
    case "sat" => true
    case _ => false
  }
}
