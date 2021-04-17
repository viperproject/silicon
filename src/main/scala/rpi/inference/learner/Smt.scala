// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner

import com.typesafe.scalalogging.LazyLogging
import fastparse.Parsed

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.Paths
import viper.silver.ast
import viper.silver.verifier.{ConstantEntry, ModelParser}

class Smt(z3: String) extends LazyLogging {
  /**
    * The z3 process.
    */
  private val process: Process = {
    // check whether the z3 file exists and whether it is executable.
    val filename = z3
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
    logger.debug(line)
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
    // writeLine("(set-option :model.completion false)")
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
    fastparse.parse(response, ModelParser.model(_)) match {
      case Parsed.Success(model, _) =>
        model
          .entries
          .view
          .mapValues {
            case ConstantEntry("true") => true
            case ConstantEntry("false") => false
          }
          .toMap
    }
  }

  def solve(constraints: Seq[ast.Exp]): Map[String, Boolean] = {
    emitCheck(constraints)
    readResponse() match {
      case "sat" => readModel()
      case response =>
        sys.error(s"unexpected response: $response")
        ???
    }
  }

  def emitCheck(constraints: Seq[ast.Exp]): Unit = {
    // enter new scope
    writeLine("(push)")
    // declare variables
    constraints
      .flatMap { constraint =>
        constraint.collect { case variable: ast.LocalVar => variable.name }
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

  def convert(exp: ast.Exp): String = exp match {
    case ast.TrueLit() => "true"
    case ast.FalseLit() => "false"
    case ast.LocalVar(name, _) => name
    case ast.Not(arg) => s"(not ${convert(arg)})"
    case ast.And(left, right) => s"(and ${convert(left)} ${convert(right)})"
    case ast.Or(left, right) => s"(or ${convert(left)} ${convert(right)})"
    case ast.Implies(left, right) => s"(=> ${convert(left)} ${convert(right)})"
    case ast.EqCmp(left, right) => s"(= ${convert(left)} ${convert(right)})"
    case _ => ???
  }
}
