// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.annotation

import rpi.inference.Hypothesis
import rpi.inference.context.Instance
import rpi.util.ast.Expressions._
import rpi.util.ast._
import viper.silver.ast

/**
  * Syntactic analysis to determine depth up to which fields are accessed.
  */
object AccessAnalysis {
  type Depth = Hypothesis => Int

  /**
    * Returns a depth function that, provided a hypothesis, computes the maximal depth up to which fields are accessed
    * by the given statement.
    *
    * @param statement The statement.
    * @return The depth function.
    */
  def accessDepth(statement: ast.Stmt): Depth = {
    val initial = FunctionState.bottom
    val result = run(statement, initial)
    result.value
  }

  /**
    * Returns the maximal depth up to which fields are accessed by the given expression.
    *
    * @param expression The expression.
    * @return The depth up to which fields are accessed.
    */
  def accessDepth(expression: ast.Exp): Int =
    fields(expression)
      .foldLeft(0) { (result, field) =>
        math.max(result, getDepth(field))
      }

  /**
    * Returns the field accesses appearing in the given expression.
    *
    * @param expression The expression.
    * @return The field accesses.
    */
  def fields(expression: ast.Exp): Seq[ast.FieldAccess] =
    expression match {
      case ast.UnExp(argument) =>
        fields(argument)
      case ast.BinExp(left, right) =>
        fields(left) ++ fields(right)
      case ast.FieldAccessPredicate(field, _) =>
        Seq(field)
      case field: ast.FieldAccess =>
        Seq(field)
      case _ =>
        Seq.empty
    }

  /**
    * Runs the analysis on the given statement with the given starting state.
    *
    * @param statement The statement.
    * @param state     The starting state.
    * @tparam S The type of the state.
    * @return The resulting state.
    */
  private def run[S <: State[S]](statement: ast.Stmt, state: S): S =
    statement match {
      case ast.Seqn(statements, _) =>
        statements.foldRight(state) { (current, result) => run(current, result) }
      case ast.If(_, left, right) =>
        run(left, state) join run(right, state)
      case Hinted(body, _) =>
        run(body, state)
      case _ =>
        state.execute(statement)
    }

  /**
    * An analysis state.
    *
    * @tparam S The type of the state.
    */
  private trait State[S <: State[S]] {
    self: S =>

    def value: Depth

    /**
      * Returns the bottom state.
      *
      * @return The bottom state.
      */
    def bottom: S

    /**
      * Returns the join of the two given states.
      *
      * @param left  The left state.
      * @param right The right state.
      * @return The join.
      */
    def join(left: S, right: S): S

    /**
      * Returns the join of this and the given other state.
      *
      * @param other The other state.
      * @return The join.
      */
    def join(other: S): S =
      join(self, other)

    /**
      * Returns the state obtained by executing the given statement in this state.
      *
      * @param statement The statement.
      * @return The resulting state.
      */
    def execute(statement: ast.Stmt): S
  }

  private object FunctionState {
    val bottom: FunctionState =
      FunctionState(0)

    def apply(depth: Int): FunctionState =
      FunctionState(Function.const(depth): Depth)

    def apply(depth: Depth): FunctionState =
      new FunctionState(depth)
  }

  /**
    * A simple state holding a depth function.
    */
  private class FunctionState(val value: Depth) extends State[FunctionState] {
    self =>

    override def bottom: FunctionState =
      FunctionState.bottom

    override def join(left: FunctionState, right: FunctionState): FunctionState =
      FunctionState(max(left.value, right.value))

    override def execute(statement: ast.Stmt): FunctionState =
      statement match {
        case ast.LocalVarAssign(_, value) =>
          self.read(value)
        case ast.FieldAssign(target, value) =>
          if (target.typ == ast.Ref) {
            val targetDepth = accessDepth(target)
            val valueDepth = accessDepth(value)
            val maximum = math.max(targetDepth, valueDepth)
            val delta = targetDepth - valueDepth
            self.increase(delta).bound(maximum)
          } else {
            // read target and value
            self.read(target).read(value)
          }
        case ast.NewStmt(_, _) =>
          self
        case ast.Inhale(_) =>
          self
        case ast.Exhale(expression) =>
          expression match {
            case placeholder: ast.PredicateAccessPredicate =>
              val instance = Infos.value[Instance](placeholder)
              self.read(instance)
            case _ =>
              self.read(expression)
          }
        case Cut(_) =>
          self
      }

    private def read(instance: Instance): FunctionState =
      self join FunctionState(hypothesis => {
        val body = hypothesis.getPredicateBody(instance)
        accessDepth(body)
      })

    private def read(expression: ast.Exp): FunctionState =
      bound(accessDepth(expression))

    /**
      * Bounds the depth from below by the given amount.
      *
      * @param depth The depth bound.
      * @return The resulting state.
      */
    private def bound(depth: Int): FunctionState =
      if (depth == 0) self
      else self join FunctionState(depth)

    /**
      * Increases the depth by the given amount.
      *
      * @param delta The depth increase.
      * @return The resulting state.
      */
    private def increase(delta: Int): FunctionState =
      if (delta <= 0) self
      else FunctionState(hypothesis => value(hypothesis) + delta)
  }

  /**
    * Returns the maximum of the two given depth functions.
    *
    * @param left  The left depth function.
    * @param right The right depth function.
    * @return The maximum.
    */
  private def max(left: Depth, right: Depth): Depth =
    hypothesis => math.max(left(hypothesis), right(hypothesis))
}