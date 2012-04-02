package ch.ethz.inf.pm.silicon
package reporting

import silAST.{ASTNode => SILASTNode}
import silAST.source.{
    SourceLocation => SILSourceLocation,
    noLocation => SILNoLocation}
import interfaces.reporting.{Categorie, Reason, Message}

sealed abstract class AbstractMessage extends Message {
	protected def majorCode: Int
	protected def majorText: String
	
	var loc: SILSourceLocation = SILNoLocation
	var reason: Option[Reason] = None
	var reasonFixed: Boolean = false
	var details: Seq[Any] = Nil
	
	def at(loc: SILSourceLocation) = {
		this.loc = loc
		this
	}	
	
	def withDetails(details: Any*) = {
		this.details = details
		this
	}
	
	def dueTo(reason: Reason) = dueTo(reason, false)
	
	def dueTo(reason: Reason, fixReason: Boolean = false) = {
		if (!reasonFixed || this.reason == None) this.reason = Some(reason)
		reasonFixed = fixReason
		this
	}
	
  def code =
		majorCode + (if (reason.isDefined)
                  reason.get.code
                else
                  0)
                  
  def text = format

	def format = {
		var str = "%s %s:".format(cat.name, code)
		
		if (loc != SILNoLocation)
			str += " %s:".format(loc)
			
		str += " " + majorText.format(details: _*)
		
		if (reason.isDefined)
			str += " " + reason.get.text

		str
	}

	override def toString = format
}

case class ErrorMessage(majorCode: Int, majorText: String) extends AbstractMessage
	{ val cat = Categories.Error }

case class WarningMessage(majorCode: Int, majorText: String) extends AbstractMessage
	{ val cat = Categories.Warning }

trait RedirectAtToWithDetails extends AbstractMessage {
	override def at(loc: SILSourceLocation) = withDetails(loc.toString)
}

/* ATTENTION: Increase error message codes in steps of at least 100 in order to
 *            not conflict with reason codes.
 */
object ErrorMessages {
	def NotSupported = ErrorMessage(50, "Not supported: %s.")
	def ExecutionFailed = ErrorMessage(70, "Symbolic execution failed.")
	
	def FractionMightBeNegative =
		ErrorMessage(130, "Fraction might be negative while accessing %s.%s.")
		
	def FractionMightBeGT100 =
		ErrorMessage(140, "Fraction might be greater than 100 while accessing %s.%s.")
	
	// def InvocationFailed(fapp: FunctionApplication): ErrorMessage =
		// InvocationFailed(fapp.obj, fapp.id, fapp)
		
	// def InvocationFailed(call: Call): ErrorMessage =
		// InvocationFailed(call.obj, call.id, call)
		
	// def InvocationFailed(fapp: FunctionApplication): ErrorMessage =
		// InvocationFailed(fapp.obj, fapp.id, fapp)
		
	// def InvocationFailed(call: Call): ErrorMessage =
		// InvocationFailed(call.obj, call.id, call)
		
	def InvocationFailed(id: String, pos: SILSourceLocation) = {
		val err = new ErrorMessage(200, "Invocation of " + id +
				" failed at %s.") with RedirectAtToWithDetails

		err.loc = pos
		err
	}		
		
	// def ForkFailed(call: CallAsync): ErrorMessage =
		// InvocationFailed(call.obj, call.id, call)

	def PostconditionMightNotHold = ErrorMessage(300, "Postcondition might not hold.")
	
	def AssertionMightNotHold(pos: SILSourceLocation) = {
		val err = new ErrorMessage(400, "Assertion might not hold at %s.")
				with RedirectAtToWithDetails
		
		err.loc = pos
		err
	}
	
	def HeapReadFailed = ErrorMessage(500, "Heap read failed.")
	def HeapWriteFailed = ErrorMessage(600, "Heap write failed.")
	
	def FoldingFailed(pos: SILSourceLocation) = {
		val err = new ErrorMessage(700, "Folding failed at %s.")
				with RedirectAtToWithDetails

		err.loc = pos
		err
	}
	
	def UnfoldingFailed = ErrorMessage(800, "Unfolding failed.")
	def JoinFailed = ErrorMessage(900, "Joining %s failed.")
	
	def SpecsMalformed = ErrorMessage(1000, "Specs of %s are malformed.")

	def ShareFailed(obj: String) =
		ErrorMessage(1100, "Sharing %s failed.".format(obj))
		
	def AcquireFailed(obj: String) =
		ErrorMessage(1200, "Acquiring %s failed.".format(obj))

	def ReleaseFailed(obj: String) =
		ErrorMessage(1300, "Releasing %s failed.".format(obj))
		
	def InvalidLockBounds =
		ErrorMessage(1400, "A lower bound might not be smaller than an upper bound.")
		
	def UnshareFailed(obj: String) =
		ErrorMessage(1500, "Unsharing %s failed.".format(obj))
		
	def MonitorInvariantMightNotHold(pos: SILSourceLocation) = {
		val err = new ErrorMessage(1600, "Monitor invariant might not hold at %s.")
				 with RedirectAtToWithDetails

		err.loc = pos
		err
	}
		
	def LoopBodyFailed(pos: SILSourceLocation) = {
		val err = new ErrorMessage(1800, "Loop body verification failed at %s.")
				with RedirectAtToWithDetails
		
		err.loc = pos
		err
	}
	
	def LoopInvNotPreserved =
		new ErrorMessage(1900, "Loop invariant might not be preserved by the loop.")

	def LoopInvNotEstablished =
		new ErrorMessage(2000, "Loop invariant might not hold on entry of the loop.")
		
	// def SendFailed(send: Send) = {
	def SendFailed(pos: SILSourceLocation) = {
		val err = new ErrorMessage(2100, "Send at %s failed.") with RedirectAtToWithDetails
		
		err.loc = pos
		err
	}
	
	def ReceiveFailed(ch: String) = new ErrorMessage(2200, "Receiving from %s failed.".format(ch))
}

object WarningMessages {
	def NotSupported = WarningMessage(5100, "Not supported: %s.")
	
	def SmokeDetected =
		WarningMessage(5200, "Path conditions became inconsistent after adding %s.")
													
	def ExcludingUnit = WarningMessage(5300, "Excluding %s.")
	
	// def SmokeDetectedAtChunkLookup = 
		// WarningMessage(5400, "Detected inconsistent state looking up a chunk for %s.%s.")
}

case class DefaultReason(val code: Int, val text: String) extends Reason {
	def format =
		"%s: %s".format(code, text)
		
	override def toString = format
}

/* ATTENTION: Since error messages increase in steps of 100, reason codes
 *            must not be >= 100 in order to avoid ambiguity.
 */
object Reasons {
	def ReceiverMightBeNull(e0: String, id: String): DefaultReason =
		ReceiverMightBeNull("member access %s.%s".format(e0, id))
		
	def ReceiverMightBeNull(detail: String): DefaultReason =
		DefaultReason(5, "Receiver of %s might be null.".format(detail))
		
	def ExpressionMightEvaluateToFalse =
		DefaultReason(10, "Expression might evaluate to false.")
		
	val TokenNotWriteable = DefaultReason(20, "Token is not writeable.")				
	
	def InsufficientPermissions(e0: String, id: String) =
		DefaultReason(30, "Insufficient permissions to access %s.%s.".format(e0, id))
		
	def InsufficientLockchange =
		DefaultReason(40, "Lockchange set might not contain all changed locks.")

	def ObjectMightBeShared =	
		DefaultReason(42, "Object might already be shared.")
		
	def ObjectMightBeLocked =	
		DefaultReason(45, "Object might already be locked.")
		
	def ObjectMightNotBeLocked(lm: String) =
		DefaultReason(46, "Object might not be %s-locked.".format(lm))
		
	def MethodLeavesDebt = DefaultReason(50, "Method might leave a debt.")
		
	def ChannelMightBeNull = DefaultReason(60, "Channel might be null.")
	
	def OperationRequiresCredits =
		DefaultReason(70, "The operation requires a credit.")
		
	def MightNotBeAboveWaitlevel =
		DefaultReason(80, "waitlevel << mu might not hold.")
}

object utils {
	implicit def nodeToLocation(node: SILASTNode): SILSourceLocation =
		node.sourceLocation
}