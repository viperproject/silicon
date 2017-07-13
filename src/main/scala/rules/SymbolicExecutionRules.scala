/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.state.terms.Term

trait SymbolicExecutionRules extends Immutable

trait ConsumptionResult {
  def isComplete: Boolean
  def ||(other: => ConsumptionResult): ConsumptionResult
}

case class Complete() extends ConsumptionResult {
  override def isComplete: Boolean = true
  override def ||(other: => ConsumptionResult): ConsumptionResult = this
}

case class Incomplete(permsNeeded: Term) extends ConsumptionResult {
  override def isComplete: Boolean = false
  override def ||(other: => ConsumptionResult): ConsumptionResult = other
}