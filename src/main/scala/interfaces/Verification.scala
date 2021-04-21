// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces

import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.Term
import viper.silicon.state.{State, Store}
import viper.silver.verifier.{Counterexample, Model, VerificationError}

/*
 * Results
 */
class VerificationResultWrapper(verificationResultsarg: Seq[VerificationResult]) {
  def verificationResults: Seq[VerificationResult] = verificationResultsarg

  def &&(other: => VerificationResultWrapper): VerificationResultWrapper = {
    //Filter out multiple Successes
    var combinedSeq = this.verificationResults ++ other.verificationResults
    val hasSuccess = combinedSeq.contains(Success())
    combinedSeq = combinedSeq flatMap {
      case _: Success => None
      case vr: VerificationResult => Some(vr)
    }
    if (combinedSeq.isEmpty && hasSuccess) combinedSeq = Seq(Success())
    new VerificationResultWrapper(combinedSeq)
  }
  // short circuit "and"
  def &&&(other: => VerificationResultWrapper): VerificationResultWrapper = { //TODO:J check if this is really needed
    if (this.containsFatal) this else this && other
  }
  def getFatals: Seq[FatalResult] = verificationResults flatMap{
     case fr: FatalResult => Some(fr)
     case _ => None
  }
  def getFailures: Seq[Failure] = verificationResults flatMap {
    case fl: Failure => Some(fl)
    case _ => None
  }
  def containsFatal: Boolean = verificationResults.foldLeft(false)((b: Boolean,v: VerificationResult)=>b || v.isFatal)
  def containsFailure: Boolean = getFailures.nonEmpty
}

object VerificationResultWrapper {
  def apply(vr: VerificationResult): VerificationResultWrapper = new VerificationResultWrapper(Seq(vr))
  def apply(vrs: Seq[VerificationResult]): VerificationResultWrapper = new VerificationResultWrapper(vrs)

  def unapply(arg: VerificationResultWrapper): Option[Seq[VerificationResult]] = Some(arg.verificationResults)
//  def unapply(vrw: VerificationResultWrapper): Option[Seq[VerificationResult]] = if (vrw.verificationResults.nonEmpty) Some(vrw.verificationResults) else None
//  def unapply(vr: VerificationResult): Option[VerificationResult] = Some(vr) //TODO:J check how this could work
}


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

trait SiliconCounterexample extends Counterexample {
  val internalStore: Store
  def store: Map[String, Term] = internalStore.values.map{case (k, v) => k.name -> v}
  def withStore(s: Store) : SiliconCounterexample
}

case class SiliconNativeCounterexample(internalStore: Store, heap: Iterable[Chunk], oldHeap: Option[Iterable[Chunk]], model: Model) extends SiliconCounterexample {
  override def withStore(s: Store): SiliconCounterexample = {
    SiliconNativeCounterexample(s, heap, oldHeap, model)
  }
}

case class SiliconRawCounterexample(conditions: Seq[Term], state: State, model: Model) extends SiliconCounterexample {
  override val internalStore: Store = state.g
  override def withStore(s: Store): SiliconCounterexample = copy(state = state.copy(g = s))
}

case class SiliconVariableCounterexample(internalStore: Store, nativeModel: Model) extends SiliconCounterexample {
  override val model: Model = {
    Model(internalStore.values.filter{
      case (_,v) => nativeModel.entries.contains(v.toString)
    }.map{
      case (k, v) => k.name -> nativeModel.entries(v.toString)
    })
  }
  override def withStore(s: Store): SiliconCounterexample = {
    SiliconVariableCounterexample(s, nativeModel)
  }
}

