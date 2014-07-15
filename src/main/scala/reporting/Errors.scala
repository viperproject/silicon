/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package reporting

import viper.silver.verifier.AbstractError

/* TODO: Distinguish between the exception that can be thrown and the error that is reported back to e.g. Scala2Sil. */
case class Z3InteractionFailed(message: String) extends RuntimeException(message) with AbstractError {
  def pos = ast.NoPosition
  def fullId = "z3.interaction.failed"
  def readableMessage = s"Interaction with Z3 failed: $message"
}

case class VerificationException(error: AbstractError) extends RuntimeException(error.readableMessage)
