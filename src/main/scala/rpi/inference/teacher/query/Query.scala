// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.teacher.query

import rpi.inference.context.Instance
import viper.silver.ast

/**
  * A query.
  *
  * @param program   The program.
  * @param snapshots The snapshots representing labels and specification instances of all inhaled and exhaled state
  *                  snapshots. Since the labels were added in topological order with respect to the control flow, for
  *                  any actual execution, the encountered labels are guaranteed to appear in order (note: there are no
  *                  loops as they are handled modularly).
  * @param names     The names.
  */
class Query(val program: ast.Program, val snapshots: Seq[(String, Instance)], names: Map[String, Map[ast.Exp, String]]) {
  /**
    * Returns the name associated with the given expression in the state snapshot with the given label.
    *
    * @param label      The snapshot label.
    * @param expression The expression.
    * @return The name associated with the expression.
    */
  def name(label: String, expression: ast.Exp): String =
    names(label)(expression)
}

/**
  * A partial query.
  */
class PartialQuery {
  /**
    * The snapshots.
    */
  private var snapshots: Seq[(String, Instance)] =
    Seq.empty

  /**
    * The names.
    */
  private var names: Map[String, Map[ast.Exp, String]] =
    Map.empty

  /**
    * Finalizes the query with the given program.
    *
    * @param program The program.
    * @return The finalized query.
    */
  def apply(program: ast.Program): Query =
    new Query(program, snapshots, names)

  /**
    * Adds a state snapshot with the given label and specification instance.
    *
    * @param label    The snapshot label.
    * @param instance The instance.
    */
  def addSnapshot(label: String, instance: Instance): Unit =
    snapshots = snapshots :+ (label, instance)

  /**
    * Associates the given expression with the given name in the state snapshot with the given label.
    *
    * @param label      The snapshot label.
    * @param expression The expression.
    * @param name       The name.
    */
  def addName(label: String, expression: ast.Exp, name: String): Unit = {
    val added = names
      .getOrElse(label, Map.empty)
      .updated(expression, name)
    names = names.updated(label, added)
  }

  /**
    * @see [[Query.name]]
    */
  def name(label: String, expression: ast.Exp): String =
    names(label)(expression)
}