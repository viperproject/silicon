/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.reporting

import viper.silver.ast
import viper.silver.verifier.AbstractError

case class Z3InteractionFailed(message: String) extends RuntimeException(message) with AbstractError {
  def pos = ast.NoPosition
  def fullId = "z3.interaction.failed"
  def readableMessage = s"Interaction with Z3 failed: $message"
}

case class VerificationException(error: AbstractError) extends RuntimeException(error.readableMessage)
