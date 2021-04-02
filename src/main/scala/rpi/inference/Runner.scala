// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference

import rpi.Configuration
import rpi.util.ast.Parser
import viper.silver.ast

/**
  * A trait providing useful methods to run the inference.
  *
  * @tparam R The result type of the runner.
  */
trait Runner[R] {
  /**
    * Returns all phases of the inference runner.
    *
    * @return All phases.
    */
  protected def phases: Phase[String, R] =
    prePhase >> mainPhase >> postPhase

  /**
    * Returns the main phase of the runner. Usually this is just the inference phase.
    *
    * @return The main phase.
    */
  protected def mainPhase: Phase[ast.Program, ast.Program] =
    InferencePhase

  /**
    * Returns the phase that precede the main phase. Usually this is just the parsing phase.
    *
    * @return The phase preceding the main phase.
    */
  protected def prePhase: Phase[String, ast.Program] =
    ParsePhase

  /**
    * Returns the phase that succeeds the main phase. This phase usually computes the result.
    *
    * @return The phase succeeding the main phase.
    */
  protected def postPhase: Phase[ast.Program, R]

  /**
    * Runs the inference with the given arguments.
    *
    * @param arguments The arguments to the inference.
    * @return The result of the inference runner.
    */
  def run(arguments: Seq[String]): R = {
    val configuration = new Configuration(arguments)
    run(configuration)
  }

  /**
    * Runs the inference with the given configuration.
    *
    * @param configuration The configuration.
    * @return The result of the inference runner.
    */
  def run(configuration: Configuration): R = {
    // create and start inference
    implicit val inference: Inference = new Inference(configuration)
    inference.start()

    // run phases
    val input = configuration.path()
    val result = phases.run(input)

    // stop inference
    inference.stop()

    // return result
    result
  }
}

/**
  * An inference runner that prints the annotated program.
  */
trait PrintRunner extends Runner[Unit] {
  override protected def postPhase: Phase[ast.Program, Unit] =
    MapPhase(input => println(input))
}

/**
  * An inference runner that verifies the annotated program.
  */
trait TestRunner extends Runner[Boolean] {
  override protected def postPhase: Phase[ast.Program, Boolean] =
    VerificationPhase
}

/**
  * A phase of the inference runner.
  *
  * @tparam I The input type.
  * @tparam R The result type.
  */
trait Phase[I, R] {
  /**
    * Runs the phase.
    *
    * @param input     The input to the phase.
    * @param inference The implicitly passed inference.
    * @return The result computed by the phase.
    */
  def run(input: I)(implicit inference: Inference): R

  def runAll(inputs: Seq[I])(implicit inference: Inference): Seq[R] =
    inputs.map { input => run(input) }

  /**
    * Combines this and the other phase to a single phase that first runs this phase and then the other phase.
    *
    * @param other The other phase.
    * @tparam R2   The result type of the other phase.
    * @return The combined phase.
    */
  def >>[R2](other: Phase[R, R2]): Phase[I, R2] =
    PairedPhases(this, other)
}

/**
  * Pairs two phases.
  *
  * @param first  The first phase.
  * @param second The second phase.
  * @tparam I     The input type of the first phase.
  * @tparam I2    The input type of the second phase.
  * @tparam R     The result type of the second phase.
  */
case class PairedPhases[I, I2, R](first: Phase[I, I2], second: Phase[I2, R]) extends Phase[I, R] {
  override def run(input: I)(implicit inference: Inference): R =
    second.run(first.run(input))
}

/**
  * A phase that maps the input using a function.
  *
  * @param function The function.
  * @tparam I       The input type.
  * @tparam R       The result type.
  */
case class MapPhase[I, R](function: I => R) extends Phase[I, R] {
  override def run(input: I)(implicit inference: Inference): R =
    function(input)
}

/**
  * A phase that parses an input file.
  */
case object ParsePhase extends Phase[String, ast.Program] {
  override def run(input: String)(implicit inference: Inference): ast.Program =
    Parser.parse(input)
}

/**
  * A phase that infers specifications and annotates the input program.
  */
case object InferencePhase extends Phase[ast.Program, ast.Program] {
  override def run(input: ast.Program)(implicit inference: Inference): ast.Program = {
    val annotated = inference.run(input)
    // return annotated program
    annotated
  }
}

/**
  * A phase that verifies the input program.
  */
case object VerificationPhase extends Phase[ast.Program, Boolean] {
  override def run(input: ast.Program)(implicit inference: Inference): Boolean = {
    println(input)
    inference.doesVerify(input)
  }
}