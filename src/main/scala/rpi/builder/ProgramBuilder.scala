// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.builder

import rpi.util.ast.Expressions._
import rpi.util.ast.Statements._
import viper.silver.ast

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * A program builder.
  */
trait ProgramBuilder {
  /**
    * The magic fields that enables fold / unfold heuristics
    */
  protected val magic: ast.Field = ast.Field("__CONFIG_HEURISTICS", ast.Bool)()

  /**
    * The buffer used to accumulate statements for the current scope.
    */
  private var buffer: mutable.Buffer[ast.Stmt] = _

  /**
    * Adds the given statement to the current scope.
    *
    * @param statement The statement to add.
    */
  @inline
  protected def addStatement(statement: ast.Stmt): Unit =
    buffer.append(statement)

  /**
    * Collects and returns all statements produced by the given function.
    *
    * @param generate The function generating the statements.
    * @return The statements.
    */
  protected def scoped(generate: => Unit): Seq[ast.Stmt] = {
    // save outer buffer and create and set current one
    val outer = buffer
    val current = ListBuffer.empty[ast.Stmt]
    buffer = current
    // generate inner statements
    generate
    // restore old buffer and return generated scope
    buffer = outer
    current.toSeq
  }

  /**
    * Creates and returns a sequence containing the statements produced by the given function.
    *
    * @param generate The function generating the statements.
    * @return The sequence.
    */
  protected def makeScope(generate: => Unit): ast.Seqn =
    makeSequence(scoped(generate))

  protected def addConditional(conditions: Seq[ast.Exp], thenBody: ast.Stmt, elseBody: => ast.Stmt = makeSkip): Unit =
    if (conditions.isEmpty) addStatement(thenBody)
    else addConditional(makeAnd(conditions), thenBody, elseBody)

  @inline
  protected def addConditional(condition: ast.Exp, thenBody: ast.Stmt, elseBody: ast.Stmt): Unit =
    addStatement(makeConditional(condition, thenBody, elseBody))

  @inline
  protected def addLoop(condition: ast.Exp, body: ast.Stmt, invariants: Seq[ast.Exp] = Seq.empty): Unit =
    addStatement(makeLoop(condition, body, invariants))

  @inline
  protected def addAssign(target: ast.LocalVar, value: ast.Exp): Unit =
    addStatement(makeAssign(target, value))

  @inline
  protected def addInhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): Unit =
    addStatement(makeInhale(expression, info))

  @inline
  protected def addExhale(expression: ast.Exp, info: ast.Info = ast.NoInfo): Unit =
    addStatement(makeExhale(expression, info))

  @inline
  protected def addUnfold(predicate: ast.PredicateAccessPredicate): Unit =
    addStatement(ast.Unfold(predicate)())

  @inline
  protected def addFold(predicate: ast.PredicateAccessPredicate, info: ast.Info = ast.NoInfo): Unit =
    addStatement(ast.Fold(predicate)(info = info))

  @inline
  protected def addLabel(name: String): Unit =
    addStatement(makeLabel(name))
}

