// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces

import viper.silicon.interfaces.state.Chunk
import viper.silicon.reporting.Converter
import viper.silicon.state.{State, Store}
import viper.silver.verifier.{Counterexample, FailureContext, Model, VerificationError}
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier
import viper.silver.ast

/*
 * Results
 */

/* TODO: Extract appropriate interfaces and then move the implementations
 *       outside of the interfaces package.
 */

/* TODO: Make VerificationResult immutable */
sealed abstract class VerificationResult {
  var previous: Vector[VerificationResult] = Vector() //Sets had problems with equality
  val continueVerification: Boolean = true

  def isFatal: Boolean
  def &&(other: => VerificationResult): VerificationResult

  /* Attention: Parameter 'other' of 'combine' is a function! That is, the following
   * statements
   *   println(other)
   *   println(other)
   * will invoke the function twice, which might not be what you really want!
   */
  def combine(other: => VerificationResult): VerificationResult = {
    if (this.continueVerification){
      val r: VerificationResult = other
      /* Result of combining a failure with a non failure should be a failure.
      *  When combining two failures, the failure with 'continueVerification'
      *  set to false (if any) should be the 'head' result */
      (this, r) match {
        case (_: FatalResult, _: FatalResult) | (_: FatalResult, _: NonFatalResult) if r.continueVerification =>
          this.previous = (this.previous :+ r) ++ r.previous
          this
        case _ =>
          r.previous = (r.previous :+ this) ++ this.previous
          r
      }
    } else this
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
    r.previous = (r.previous :+ this) ++ this.previous
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
                  (message: VerificationError, override val continueVerification: Boolean = true)
  extends FatalResult {

  /* TODO: Mutable state in a case class? DOOOOOOOOOOOOOON'T! */
  var load: Option[Seq[Term]] = None
  def withLoad(load: Seq[Term]) = {
    this.load = Some(load)
    this
  }

  override lazy val toString = message.readableMessage
}

case class SilFailureContext(branchConditions: Seq[ast.Exp], counterExample: Option[Counterexample]) extends FailureContext {
  lazy val branchConditionString = if(branchConditions.nonEmpty)
    ("\n\t\tunder branch conditions:\n" +
      branchConditions.map(bc => (bc.toString + " [ " + bc.pos.toString + " ] ")).mkString("\t\t"," ~~> ","") ) else ""
  lazy val counterExampleString = if(counterExample.isDefined) "\n\t\tcounterexample:\n" + counterExample.get.toString else ""
  override lazy val toString = branchConditionString + counterExampleString
}

trait SiliconCounterexample extends Counterexample {
  val internalStore: Store
  lazy val store: Map[String, Term] = internalStore.values.map{case (k, v) => k.name -> v}
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

case class SiliconMappedCounterexample(
    internalStore: Store,
    heap: Iterable[Chunk],
    oldHeaps: State.OldHeaps,
    nativeModel: Model
) extends SiliconCounterexample {

  val converter: Converter =
    Converter(nativeModel, internalStore, heap, oldHeaps)

  val model: Model = nativeModel

  override lazy val toString: String = {
    val buf = converter.modelAtLabel
      .map(x => s"model at label: ${x._1}\n${x._2.toString}\n")
      .mkString("\n")
    s"$buf\non return: \n${converter.extractedModel.toString}"
  }

  override def withStore(s: Store): SiliconCounterexample = {
    SiliconMappedCounterexample(s, heap, oldHeaps, nativeModel)
  }
}
