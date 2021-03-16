// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference

import ch.qos.logback.classic.{Level, Logger}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.LoggerFactory
import rpi.builder.ProgramExtender
import rpi.inference.context.Context
import rpi.Configuration
import rpi.inference.learner.Learner
import rpi.inference.teacher.Teacher
import viper.silicon.Silicon
import viper.silver.ast
import viper.silver.verifier.{Success, VerificationResult, Verifier}

import scala.annotation.tailrec

/**
  * An inference with a configuration.
  *
  * @param configuration The configuration.
  */
class Inference(val configuration: Configuration) extends LazyLogging {

  import configuration._

  /**
    * The instance of the silicon verifier used to generate the samples.
    */
  val verifier: Verifier = {
    // create instance
    val instance = new Silicon()
    // pass arguments
    val arguments = Seq(
      "--z3Exe", configuration.z3(),
      "--counterexample", "raw",
      "--enableMoreCompleteExhale",
      "--ignoreFile", "dummy.vpr")
    instance.parseCommandLine(arguments)
    // return instance
    instance
  }

  /**
    * Starts the inference and all of its subcomponents.
    */
  def start(): Unit = {
    // set log level
    configuration
      .logLevel
      .foreach { option => setLogLevel(org.slf4j.Logger.ROOT_LOGGER_NAME, Level.toLevel(option)) }

    // debug logging
    setLogLevel("rpi.inference.learner.GuardEncoder", Level.DEBUG)
    setLogLevel("rpi.inference.learner.Smt", Level.DEBUG)

    verifier.start()
  }

  private def setLogLevel(name: String, level: Level): Unit =
    LoggerFactory
      .getLogger(name)
      .asInstanceOf[Logger]
      .setLevel(level)

  /**
    * Stops the inference and all of its subcomponents.
    */
  def stop(): Unit = {
    verifier.stop()
  }

  /**
    * Runs the inference on the given program.
    *
    * @param program The input program.
    * @return The program annotated with the inferred specifications.
    */
  def run(program: ast.Program): ast.Program = {
    // create context, learner, teacher, and learner
    val context = new Context(inference = this, program)
    val teacher = new Teacher(context)
    val learner = new Learner(context)

    // start teacher and learner
    teacher.start()
    learner.start()

    /**
      * Helper method that iteratively refines the hypothesis.
      *
      * @param round The current round.
      * @return The ultimate hypothesis.
      */
    @tailrec
    def infer(round: Int = 0): Hypothesis = {
      // compute hypothesis
      val hypothesis = learner.hypothesis
      logger.info("--- current hypothesis ---")
      hypothesis.predicates.foreach { predicate => logger.info(predicate.toString()) }
      if (round >= maxRounds()) hypothesis
      else {
        logger.info(s"\n----- start round #$round -----\n")
        // check hypothesis
        val samples = teacher.check(hypothesis)
        if (samples.isEmpty) hypothesis
        else {
          // add samples and iterate
          logger.info("--- add samples ---")
          samples.foreach { sample =>
            logger.info(sample.toString)
            learner.addSample(sample)
          }
          infer(round + 1)
        }
      }
    }

    // infer specifications
    val hypothesis = infer()

    // stop teacher and learner
    teacher.stop()
    learner.stop()

    // annotate program
    val extender = new ProgramExtender(context)
    extender.annotated(hypothesis)
  }

  /**
    * Verifies the given program.
    *
    * @param program The program to verify.
    * @return The verification result.
    */
  def verify(program: ast.Program): VerificationResult =
    verifier.verify(program)

  /**
    * Returns whether the given program verifies.
    *
    * @param program The program to verify.
    * @return True if the program verifies.
    */
  def doesVerify(program: ast.Program): Boolean =
    verify(program) match {
      case Success => true
      case _ => false
    }
}