package ch.ethz.inf.pm.silicon.interfaces.state

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term, Permissions}

/*
 * Chunks
 */

trait Chunk {
	def rcvr: Term
	def id: String
}
 
/* Persistent chunk remain present even when a heap is reset/emptied in 
 * order to ensure self-framing of assertions.
 */
trait PersistentChunk extends Chunk
 
trait AccessRestrictedChunk[S <: AccessRestrictedChunk[S]] extends Chunk {

	def perm: Permissions
	def +(perm: Permissions): S
	def -(perm: Permissions): S
}

trait FieldChunk extends AccessRestrictedChunk[FieldChunk] {
	def value: Term
}

/* TODO: Predicates should eventually take arguments */
trait PredicateChunk extends AccessRestrictedChunk[PredicateChunk] {
	def snap: Term
}