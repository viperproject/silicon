package semper
package silicon
package reporting

import sil.verifier.AbstractError

/* TODO: Distinguish between the exception that can be thrown and the error that is reported back to e.g. Scala2Sil. */
case class Z3InteractionFailed(message: String) extends RuntimeException(message) with AbstractError {
  def pos = ast.NoPosition
  def fullId = "z3.interaction.failed"
  def readableMessage = s"Interaction with Z3 failed: $message"
}

case class VerificationException(error: AbstractError) extends RuntimeException(error.readableMessage)
