package ch.ethz.inf.pm.silicon.interfaces

// import scala.util.parsing.input.Positional
import ch.ethz.inf.pm.silicon
import reporting.{Message, Reason}
// import silicon.ast.{Member, TopLevelDecl}

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

trait ResultWithMessage extends VerificationResult {
	def message: Message
}

case class Success() extends NonFatalResult

case class Warning(val message: Message)
		extends NonFatalResult with ResultWithMessage

case class Failure(val message: Message)
		extends FatalResult with ResultWithMessage

// /*
 // * Verification
 // */
	
// trait MemberVerifier {
	// def verify(mem: Member): VerificationResult
// }

// trait ProgrammeVerifier {
	// def verify(prog: List[TopLevelDecl]): List[VerificationResult]
// }