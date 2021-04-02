// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.teacher.state

import rpi.util.ast.Expressions.makeVariable
import rpi.util.ast.{Infos, Previous}
import viper.silicon.resources.FieldID
import viper.silicon.state.{BasicChunk, State, terms}
import viper.silicon.state.terms.sorts
import viper.silver.ast

/**
  * A helper class used to evaluate a given state.
  *
  * @param label The label of the state.
  * @param state The state.
  * @param model The model.
  */
case class StateEvaluator(label: Option[String], state: State, model: ModelEvaluator) {
  /**
    * Returns the value associated with the given variable.
    * TODO: Precompute or cache?
    *
    * @param variable The variable to look up.
    * @return The value.
    */
  private def store(variable: ast.LocalVar): String = {
    // adapt variable to state (if necessary)
    val adapted = label match {
      case Some(label) if !Infos.isSaved(variable) =>
        // adapt variable
        val name = s"${label}_${variable.name}"
        makeVariable(name, variable.typ)
      case _ =>
        // no adaption needed
        variable
    }
    // evaluate variable
    val term = state.g(adapted)
    model.evaluateReference(term)
  }

  // precomputed heap map
  private[state] val heap = label
    .map { name => state.oldHeaps(name) }
    .getOrElse(state.h)
    .values
    .foldLeft(Map.empty[String, Map[String, String]]) {
      case (result, chunk: BasicChunk) if chunk.resourceID == FieldID =>
        val term = chunk.snap
        term.sort match {
          case sorts.Ref =>
            val receiver = model.evaluateReference(chunk.args.head)
            val field = chunk.id.name
            val value = model.evaluateReference(term)
            // update field map
            val fields = result
              .getOrElse(receiver, Map.empty)
              .updated(field, value)
            // update heap
            result.updated(receiver, fields)
          case _ =>
            // do nothing
            result
        }
      case (result, _) =>
        result
    }

  // TODO: We might not need this if we switch to a partition abstraction.
  def evaluateBoolean(expression: ast.Exp): Boolean =
    expression match {
      case original@ast.BinExp(left, right) =>
        left.typ match {
          case ast.Ref =>
            // evaluate operands
            val leftReference = evaluateReference(left)
            val rightReference = evaluateReference(right)
            // reduce operands
            original match {
              case ast.EqCmp(_, _) =>
                leftReference == rightReference
              case ast.NeCmp(_, _) =>
                leftReference != rightReference
            }
          case _ => ???
        }
      case _ => ???
    }

  def evaluateBoolean(name: String): Boolean = {
    val variable = ast.LocalVar(name, ast.Bool)()
    val term = state.g(variable)
    model.evaluateBoolean(term)
  }

  def evaluatePermission(name: String): Double = {
    val variable = ast.LocalVar(name, ast.Perm)()
    val term = state.g(variable)
    model.evaluatePermission(term)
  }

  /**
    * Evaluates the given reference-typed expression.
    *
    * @param expression The expression to evaluate.
    * @return The value.
    */
  def evaluateReference(expression: ast.Exp): String =
    expression match {
      case ast.NullLit() =>
        model.evaluateReference(terms.Null())
      case variable: ast.LocalVar =>
        store(variable)
      case ast.FieldAccess(receiver, ast.Field(field, _)) =>
        val receiverValue = evaluateReference(receiver)
        heap(receiverValue)(field)
    }
}
