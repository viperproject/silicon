// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.annotation

import rpi.Names
import viper.silver.ast

object Hint {
  def apply(name: String, argument: ast.Exp, old: ast.LocalVar): Hint =
    Hint(name, Seq.empty, argument, old)
}

/**
  * A folding hint.
  *
  * @param name       The name (corresponds to an annotation).
  * @param conditions The condition under which the hint is relevant.
  * @param argument   The argument for which this hint is meant.
  * @param old        The variable holding the old value of the argument.
  */
case class Hint(name: String, conditions: Seq[ast.Exp], argument: ast.Exp, old: ast.LocalVar) {
  /**
    * Returns true if this hint corresponds to a down annotation.
    *
    * @return True if this hint corresponds to a down annotation.
    */
  def isDown: Boolean =
    name == Names.downAnnotation

  /**
    * Returns true if this hint corresponds to an up annotation.
    *
    * @return True if this hint corresponds to an up annotation.
    */
  def isUp: Boolean =
    name == Names.upAnnotation

  /**
    * Returns the hint with the given condition added.
    *
    * @param condition The condition.
    * @return The hint with the condition added.
    */
  def withCondition(condition: ast.Exp): Hint =
    copy(conditions = condition +: conditions)
}