// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.state.terms.{Forall, Term, Var}
import viper.silicon.state.terms.perms.IsNonPositive
import viper.silver.ast
import viper.silicon.verifier.Verifier

sealed trait ConsumptionResult {
  def isComplete: Boolean
  def ||(other: => ConsumptionResult): ConsumptionResult
}

private case class Complete() extends ConsumptionResult {
  override def isComplete: Boolean = true
  override def ||(other: => ConsumptionResult): ConsumptionResult = this
}

private case class Incomplete(permsNeeded: Term, permsNeededExp: Option[ast.Exp]) extends ConsumptionResult {
  override def isComplete: Boolean = false
  override def ||(other: => ConsumptionResult): ConsumptionResult = other
}

object ConsumptionResult {
  def apply(term: Term, exp: Option[ast.Exp], qvars: Seq[Var],  v: Verifier, timeout: Int): ConsumptionResult = {
    val toCheck = if (qvars.isEmpty) {
      IsNonPositive(term)
    } else {
      Forall(qvars, IsNonPositive(term), Seq())
    }
    if (v.decider.check(toCheck, timeout))
      Complete()
    else
      Incomplete(term, exp)
  }
}
