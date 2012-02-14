package ch.ethz.inf.pm.silicon

import com.weiglewilczek.slf4s.Logging

import silAST.source.{/* SourceLocation => SILSourceLocation, */ noLocation => SILNoLocation}

// import scala.util.parsing.input.NoPosition
import interfaces.{VerificationResult, Success, Warning, Failure}
import interfaces.decider.Decider
import interfaces.reporting.{Message}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk,
		FieldChunk, PredicateChunk, AccessRestrictedChunk, StateFormatter}
import state.terms.{Term, Permissions}
import state.terms.utils.{SetAnd, ¬}
import reporting.Bookkeeper
import reporting.Reasons.InsufficientPermissions
// import ast.Expression

/* TODO: Move interfaces into interfaces package */

trait HasLocalState {
	def pushLocalState() = ()
	def popLocalState() = ()
}

trait Brancher {
	def branch(ts: Term, fTrue: => VerificationResult,
						fFalse: => VerificationResult): VerificationResult
						
	def branch(ts: List[Term], fTrue: => VerificationResult,
						fFalse: => VerificationResult): VerificationResult
}

trait DefaultBrancher[V, ST <: Store[V, ST], H <: Heap[H],
                      PC <: PathConditions[PC], S <: State[V, ST, H, S]]
		extends Brancher with HasLocalState {

	val decider: Decider[V, ST, H, PC, S]
	import decider.assume
	
	val bookkeeper: Bookkeeper
	
	def branch(t: Term, fTrue: => VerificationResult,
						fFalse: => VerificationResult) =
						
		branch(t :: Nil, fTrue, fFalse)
	
	def branch(ts: List[Term], fTrue: => VerificationResult,
						fFalse: => VerificationResult) = {

		val guardsTrue = SetAnd(ts)
		val guardsFalse = SetAnd(ts, t => ¬(t))
									 
		val exploreTrueBranch = !decider.assert(guardsFalse)
		val exploreFalseBranch = !decider.assert(guardsTrue)
		
		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		// msgbus.send(IncrementBranchCounter(additionalPaths))
		bookkeeper.branches += additionalPaths
			
		((if (exploreTrueBranch) {
			// msgbus.send(PreBranching(TrueBranch)) // e.g. push caches
			// preBranchingHook()
			pushLocalState()
			val result = assume(guardsTrue, fTrue)
			// msgbus.send(PostBranching(TrueBranch)) // e.g. pop caches
			// postBranchingHook()
			popLocalState()
			result
		} else Success())
			&&
		(if (exploreFalseBranch) {
			// msgbus.send(PreBranching(FalseBranch)) // e.g. push caches
			// preBranchingHook()
			pushLocalState()
			val result = assume(guardsFalse, fFalse)
			// msgbus.send(PostBranching(FalseBranch)) // e.g. pop caches
			// postBranchingHook()
			popLocalState()
			result
		} else Success()))
	}
}

trait ChunkFinder[E, H <: Heap[H]] {
	def withChunk[CH <: Chunk](h: H, rcvr: Term, id: String, e: E, m: Message,
								Q: CH => VerificationResult): VerificationResult
	
	/* withChunk is sufficient, i.e. withFieldChunk and withPredicateChunk are
	 * redundant, because we can narrow down the required type chunk with the type
	 * parameter of withChunk.
	 */

	def withFieldChunk(h: H, rcvr: Term, id: String, e: E, m: Message,
										 Q: FieldChunk => VerificationResult): VerificationResult
								
	def withPredicateChunk(h: H, rcvr: Term, id: String, e: E, m: Message,
										   Q: PredicateChunk => VerificationResult): VerificationResult
											 
	def withFieldChunk(h: H, rcvr: Term, id: String, p: Permissions, e: E, m: Message,
									  Q: FieldChunk => VerificationResult): VerificationResult
								
	def withPredicateChunk(h: H, rcvr: Term, id: String, p: Permissions, e: E,
	                     m: Message, Q: PredicateChunk => VerificationResult)
											: VerificationResult
}

class DefaultChunkFinder[V, E, ST <: Store[V, ST],
												 H <: Heap[H], PC <: PathConditions[PC],
												 S <: State[V, ST, H, S]]
		(val decider: Decider[V, ST, H, PC, S],
		 val stateFormatter: StateFormatter[V, ST, H, S, String])
		extends ChunkFinder[E, H] with Logging {

	def withChunk[CH <: Chunk](h: H, rcvr: Term, id: String, e: E,
														 m: Message, Q: CH => VerificationResult)
														: VerificationResult = {

		decider.getChunk(h, rcvr, id) match {
			case Some(c: CH) => Q(c)
			case None =>
				// val pos = if (m.loc != SILNoLocation) m.loc else e.pos
				val pos = SILNoLocation

				if (decider.checkSmoke)	{
					logger.debug("%s: Detected inconsistent state looking up a chunk for %s.%s.".format(pos, e, id))
					logger.debug("π = " + stateFormatter.format(decider.π))

					// val warning = Warning(SmokeDetectedAtChunkLookup at pos withDetails(e, id), c)
					// warning
					Success()
				} else
					Failure(m at pos dueTo InsufficientPermissions(e.toString, id))
		}
	}
	
	def withFieldChunk(h: H, rcvr: Term, id: String, e: E, m: Message,
										 Q: FieldChunk => VerificationResult): VerificationResult =
										 
		withChunk(h, rcvr, id, e, m, Q)
		
	def withPredicateChunk(h: H, rcvr: Term, id: String, e: E, m: Message,
											 Q: PredicateChunk => VerificationResult)
											: VerificationResult =
										 
		withChunk(h, rcvr, id, e, m, Q)
		
	def withFieldChunk(h: H, rcvr: Term, id: String, p: Permissions, e: E, m: Message,
									  Q: FieldChunk => VerificationResult) =
										
		withPermissiveChunk(h, rcvr, id, p, e, m, Q)
								
	def withPredicateChunk(h: H, rcvr: Term, id: String, p: Permissions, e: E,
	                     m: Message, Q: PredicateChunk => VerificationResult) =
		
		withPermissiveChunk(h, rcvr, id, p, e, m, Q)
		
	private def withPermissiveChunk[ARC <: AccessRestrictedChunk[ARC]]
			(h: H, rcvr: Term, id: String, p: Permissions, e: E, m: Message,
			 Q: ARC => VerificationResult)
			: VerificationResult =

		withChunk(h, rcvr, id, e, m, (chunk: ARC) => {
			val pc = chunk.asInstanceOf[ARC]
			if (decider.isAsPermissive(pc.perm, p))
				Q(pc)
			else
				Failure(m dueTo InsufficientPermissions(e.toString, id))})
}