package semper
package silicon
package interfaces

import sil.verifier.VerificationError
import reporting.Context
import reporting.{Context, TraceView}
import state.{Store, Heap, State}

/*
 * Results
 */

/* TODO: Extract appropriate interfaces and then move the implementations 
 *       outside of the interfaces package.
 */
 
/* TODO: Make VerificationResult immutable */
abstract class VerificationResult {
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

abstract class FatalResult extends VerificationResult {
	val isFatal = true
	
	def &&(other: => VerificationResult) = this
}

abstract class NonFatalResult extends VerificationResult {
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

trait ContextAwareResult[C <: Context[C, ST, H, S],
                         ST <: Store[ST],
                         H <: Heap[H],
                         S <: State[ST, H, S]]
      extends VerificationResult {

	def message: VerificationError
	def context: C
}

case class Success[C <: Context[C, ST, H, S],
                   ST <: Store[ST],
                   H <: Heap[H],
                   S <: State[ST, H, S]]
                  (context: C)
		extends NonFatalResult
       with ContextAwareResult[C, ST, H, S] {
  
  context.currentBranch.addResult(this)

	val message = null /* TODO: Make an Option[Message] */
}

case class Unreachable[C <: Context[C, ST, H, S],
                       ST <: Store[ST],
                       H <: Heap[H],
                       S <: State[ST, H, S]]
                      (context: C)
    extends NonFatalResult
       with ContextAwareResult[C, ST, H, S] {

  context.currentBranch.addResult(this)

  val message = null /* TODO: Make an Option[Message] */
}

case class Failure[C <: Context[C, ST, H, S],
                   ST <: Store[ST],
                   H <: Heap[H],
                   S <: State[ST, H, S],
                   TV <: TraceView[TV, ST, H, S]]
                  (val message: VerificationError,
                   val context: C,
                   tv: TV)
		extends FatalResult
       with ContextAwareResult[C, ST, H, S] {
  
  tv.addResult(context.currentBranch, this)
}