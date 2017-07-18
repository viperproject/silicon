/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.state.terms.Term
import viper.silicon.state.terms.perms.IsNonPositive
import viper.silicon.verifier.Verifier

sealed trait ConsumptionResult {
  def isComplete: Boolean
  def ||(other: => ConsumptionResult): ConsumptionResult
}

private case class Complete() extends ConsumptionResult {
  override def isComplete: Boolean = true
  override def ||(other: => ConsumptionResult): ConsumptionResult = this
}

private case class Incomplete(permsNeeded: Term) extends ConsumptionResult {
  override def isComplete: Boolean = false
  override def ||(other: => ConsumptionResult): ConsumptionResult = other
}

object ConsumptionResult {
  def apply(term: Term, v: Verifier): ConsumptionResult = {
    if (v.decider.check(IsNonPositive(term), Verifier.config.checkTimeout()))
      Complete()
    else
      Incomplete(term)
  }
}
