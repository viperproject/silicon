// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.builder

import rpi.{Configuration, Names}
import rpi.inference.context.{Check, Context}
import rpi.inference.Hypothesis
import rpi.inference.annotation.Hint
import rpi.util.ast.{Cut, Hinted}
import viper.silver.ast

/**
  * A mixin providing methods to build programs from checks.
  */
trait CheckExtender extends ProgramBuilder {
  /**
    * Returns the context.
    *
    * @return The context.
    */
  protected def context: Context

  /**
    * Returns the configuration.
    *
    * @return The configuration.
    */
  protected def configuration: Configuration =
    context.configuration

  /**
    * The current check.
    */
  private var current: Check = _

  /**
    * Returns the check currently being processed.
    *
    * @return The current check.
    */
  protected def check: Check =
    current

  /**
    * Processes the given check, i.e., processes all instrumented statements appearing in the check.
    *
    * @param check      The check to process.
    * @param hypothesis The current hypothesis.
    * @return The body of the processed check.
    */
  protected def processCheck(check: Check, hypothesis: Hypothesis): ast.Seqn = {
    // save and update current check
    val outer = current
    current = check
    // compute result
    val result = processSequence(check.body)(hypothesis)
    // restore current check and return result
    current = outer
    result
  }

  /**
    * Processes the given sequence, i.e., processes all instrumented statements appearing in the sequence.
    *
    * @param sequence   The sequence to process.
    * @param hypothesis The implicitly passed current hypothesis.
    * @return The processed sequence.
    */
  protected def processSequence(sequence: ast.Seqn)(implicit hypothesis: Hypothesis): ast.Seqn =
    makeScope {
      sequence.ss.foreach { statement => processStatement(statement) }
    }

  /**
    * Processes the given statement, i.e., processes all instrumented statements appearing in the statement.
    *
    * @param statement  The statement to process.
    * @param hypothesis The implicitly passed current hypothesis.
    */
  protected def processStatement(statement: ast.Stmt)(implicit hypothesis: Hypothesis): Unit =
    statement match {
      case sequence: ast.Seqn =>
        addStatement(processSequence(sequence))
      case ast.If(condition, thenBody, elseBody) =>
        val instrumentedThen = processSequence(thenBody)
        val instrumentedElse = processSequence(elseBody)
        addConditional(condition, instrumentedThen, instrumentedElse)
      case Hinted(body, hints) =>
        processHinted(body)(hypothesis, hints)
      case cut: Cut =>
        processCut(cut)
      case _ =>
        addStatement(statement)
    }

  /**
    * Processes the given cut statement.
    *
    * @param cut        The cut statement.
    * @param hypothesis The implicitly passed hypothesis.
    */
  protected def processCut(cut: Cut)(implicit hypothesis: Hypothesis): Unit

  /**
    * Processes the given hinted statement.
    *
    * @param hinted     The hinted statement.
    * @param hypothesis The implicitly passed hypothesis.
    * @param hints      The implicitly passed hints.
    */
  protected def processHinted(hinted: ast.Stmt)(implicit hypothesis: Hypothesis, hints: Seq[Hint]): Unit

  /**
    * Builds and returns a program with the given extended methods and inferred predicates.
    *
    * @param extended   The extended methods.
    * @param hypothesis The hypothesis containing inferred predicates.
    * @return Teh program.
    */
  protected def buildProgram(extended: Seq[ast.Method], hypothesis: Hypothesis): ast.Program = {
    // get input program
    val input = context.input
    //  enable or disable heuristics
    val fields =
      if (configuration.useAnnotations()) input.fields
      else magic +: input.fields
    // add inferred predicates
    val predicates = {
      val existing = input.predicates
      val inferred = hypothesis.getPredicate(Names.recursive).toSeq
      existing ++ inferred
    }
    // add lemmas
    val methods = {
      val lemmas = hypothesis.getLemma(Names.appendLemma).toSeq
      lemmas ++ extended
    }
    // update program
    input.copy(fields = fields, predicates = predicates, methods = methods)(input.pos, input.info, input.errT)
  }
}