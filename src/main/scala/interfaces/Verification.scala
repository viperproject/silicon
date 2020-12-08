// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces

import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.{Store, Heap, State}
import viper.silver.verifier.{Counterexample, Model, VerificationError, SingleEntry}
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
/* counterexamples defined in silver.verifier */
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

case class SiliconMappedCounterexample(internalStore: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, nativemodel: Model) extends SiliconCounterexample {
  def storeToString : String = {
    var s = "Store: \n ------------------------------"
    for ((k,v) <- internalStore.values) {
      s = s + "\n " + k.name + " <- " + v.toString
    }
    s = s + "\n End Store"
    s
  }
  def heapToString : String = {
    var s = "Heap: \n ---------------------"
    for (chunk <- heap) {
      s = s + "\n new chunk:"
      s = s + "\n " + chunk.toString
    }
    s = s + "\n End Heap"
    s
  }

  def oldHeapToString : String = {
    var s = "Old Heaps: \n -----------------------------"
    for ((name, h) <- oldHeaps) {
      s = s + "\n name: " + name
      for (chunk <- h.values) {
        s = s + "\n " + chunk.toString
      }
    }
    s = s + "\n End Old Heaps "
    return s
  }

  override val model: Model = Model(
    nativemodel.entries 
    + (storeToString -> SingleEntry(" "))
    + (heapToString -> SingleEntry(" "))
    + (oldHeapToString -> SingleEntry(" "))
    )

  override def withStore(s: Store) : SiliconCounterexample = {
    SiliconMappedCounterexample(s, heap, oldHeaps, nativemodel)
  }
}

