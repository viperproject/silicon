/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.verifier.VerificationError
import viper.silicon.state.terms.Term

/*
 * Results
 */

/* TODO: Extract appropriate interfaces and then move the implementations
 *       outside of the interfaces package.
 */

/* TODO: Make VerificationResult immutable */
sealed abstract class VerificationResult {
  var previous: Option[NonFatalResult] = None

  def isFatal: Boolean
  def &&(other: => VerificationResult): VerificationResult

  def allPrevious: List[VerificationResult] =
    previous match {
      case None => Nil
      case Some(vr) => vr :: vr.allPrevious
    }

  def append(other: NonFatalResult): VerificationResult =
    previous match {
      case None =>
        this.previous = Some(other)
        this
      case Some(vr) =>
        vr.append(other)
    }
}

sealed abstract class FatalResult extends VerificationResult {
  val isFatal = true

  def &&(other: => VerificationResult) = this
}

sealed abstract class NonFatalResult extends VerificationResult {
  val isFatal = false

  /* Attention: Parameter 'other' of '&&' is a function! That is, the following
   * statements
   *   println(other)
   *   println(other)
   * will invoke the function twice, which might not be what you really want!
   */
  def &&(other: => VerificationResult): VerificationResult = {
    val r: VerificationResult = other
    r.append(this)
    r
  }
}

case class Success() extends NonFatalResult {
  override val toString = "Success"
}

case class Unreachable() extends NonFatalResult {
  override val toString = "Unreachable"
}

case class Failure/*[ST <: Store[ST],
                   H <: Heap[H],
                   S <: State[ST, H, S]]*/
                  (message: VerificationError)
    extends FatalResult {

  /* TODO: Mutable state in a case class? DOOOOOOOOOOOOOON'T! */
  var load: Option[Seq[Term]] = None
  def withLoad(load: Seq[Term]) = {
    this.load = Some(load)
    this
  }

  override lazy val toString = message.readableMessage
}