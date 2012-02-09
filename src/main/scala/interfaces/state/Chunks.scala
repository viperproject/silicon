package ch.ethz.inf.pm.silicon.interfaces.state

import ch.ethz.inf.pm.silicon
import silicon.state.terms.Term

/* TODO: Declare interfaces for TokenChunks and TokenSupport */

/*
 * Chunks
 */

// trait Chunk[V] {
trait Chunk {
	def rcvr: Term
	def id: String
}
 
/* Persistent chunk remain present even when a heap is reset/emptied in 
 * order to ensure self-framing of assertions.
 */
trait PersistentChunk extends Chunk
 
trait AccessRestrictedChunk[P <: Permission[P],
														S <: AccessRestrictedChunk[P, S]]
		extends Chunk {

	def perm: P
	def +(perm: P): S
	def -(perm: P): S
	
	/* The following won't work (Scala 2.8.1) since copy is a method added
	 * to case-classes by the compiler, and there is not interface that we
	 * could use here to require the existence of such a method.
	 * Hence, it will fail with "copy is not a member of Chunk".
	 */
	// def +(perm: P) = this.copy(perm = this.perm + perm)
	// def -(perm: P) = this.copy(perm = this.perm - perm)	
}

trait FieldChunk[P <: Permission[P]]
		extends AccessRestrictedChunk[P, FieldChunk[P]] {

	def value: Term
}

/* TODO: Predicates should eventually take arguments */
trait PredicateChunk[P <: Permission[P]]
		extends AccessRestrictedChunk[P, PredicateChunk[P]] {

	def snap: Term
}

/*
 * Heap support
 */

// trait FieldSupport[P <: Permission[P], S <: FieldSupport[P, S]]
	// extends Heap[S] {
	
	// def fields: Map[(Term, String), FieldChunk[P]]
// }

// trait PredicateSupport[P <: Permission[P], S <: PredicateSupport[P, S]]
		// extends Heap[S] {
		
	// def predicates: Map[(Term, String), PredicateChunk[P]]
// }
 
// trait FieldSupport[P <: Permission[P], S <: FieldSupport[P, S]]
		// extends Heap[S] {

	// trait FieldOperations {
		// // def apply[R](rcvr: Term, id: String)(f: FieldChunk[P] => R): R
		// def apply(): Iterable[FieldChunk[P]]
		// def apply(rcvr: Term, id: String): FieldChunk[P]
		// def get(rcvr: Term, id: String): Option[FieldChunk[P]]
		// def value(rcvr: Term, id: String): Term
		// // def ?(rcvr: Term, id: String): Boolean
		// def contains(rcvr: Term, id: String): Boolean
		// // def -(rcvr: Term, id: String): S
		// def remove(rcvr: Term, id: String): S
		// // def \(rcvr: Term, id: String, value: Int, perm: Int)
		// // def updated(rcvr: Term, id: String, value: Term, perm: P): S
		// // def \(c: FieldChunk[P]): S
		// def update(c: FieldChunk[P]): S
	// }
	
	// def fields: FieldOperations 
// }

// trait PredicateSupport[P <: Permission[P], S <: PredicateSupport[P, S]]
		// extends Heap[S] {

	// trait PredicateOperations {
		// def apply(): Iterable[PredicateChunk[P]]
		// def apply(rcvr: Term, id: String): PredicateChunk[P]
		// // def apply[R](rcvr: Term, id: String)(f: PredicateChunk[P] => R): R
		// def get(rcvr: Term, id: String): Option[PredicateChunk[P]]
		// def snap(rcvr: Term, id: String): Term // PredicateChunk.snap
		// // def ?(rcvr: Term, id: String): Boolean
		// def contains(rcvr: Term, id: String): Boolean
		// // def -(rcvr: Term, id: String): S
		// def remove(rcvr: Term, id: String): S
		// // def \(rcvr: Term, id: String, value: Int, perm: Int)
		// // def updated(rcvr: Term, id: String, value: Term, perm: P): S
		// // def \(c: PredicateChunk[P]): S
		// def update(c: PredicateChunk[P]): S
	// }
	
	// def predicates: PredicateOperations
// }