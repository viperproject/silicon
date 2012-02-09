package ch.ethz.inf.pm.silicon.state

import ch.ethz.inf.pm.silicon
import silicon.interfaces.state.{Heap, FieldChunk, PredicateChunk, Chunk, 
		Permission, PersistentChunk}
import silicon.state.terms.{Term, /* Token, */ Plus, Minus}

/*
 * Chunks
 */

/* TODO: Refactoring 'def +(perm: P)' and 'def -(perm: P)' 
 * 			 into an abstract base class seems
 *       to be non-straight-forward since 'copy' is a synthetic method
 *       added to case-classes by the compiler and not declared by any
 *       trait or interface.
 */

case class DefaultFieldChunk[P <: Permission[P]](rcvr: Term, id: String,
		value: Term, perm: P) extends FieldChunk[P] {
		
	def +(perm: P) = this.copy(perm = this.perm + perm)
	def -(perm: P) = this.copy(perm = this.perm - perm)
	
	override def toString = "%s.%s -> %s # %s".format(rcvr, id, value, perm)
}

case class DefaultPredicateChunk[P <: Permission[P]](rcvr: Term, id: String,
		snap: Term, perm: P) extends PredicateChunk[P] {
		
	def +(perm: P) = this.copy(perm = this.perm + perm)
	def -(perm: P) = this.copy(perm = this.perm - perm)
		
	override def toString = "%s.%s[%s] # %s".format(rcvr, id, snap, perm)
}

// case class DefaultTokenChunk[P <: Permission[P], H <: Heap[H]](rcvr: Term,
		// token: Token[P, H]) extends Chunk {

	// /* TODO: Move into companion object, so that it can be referenced 
	 // *       statically, i.e. as DefaultTokenChunk.id.
	 // */
	// val id = "$env"

	// override def toString = "%s.%s -> %s".format(rcvr, id, token)
// }

case class CounterChunk(rcvr: Term, id: String, value: Term)
		extends PersistentChunk {

	def +(t: Term) = this.copy(value = Plus(value, t))
	def -(t: Term) = this.copy(value = Minus(value, t))

	override def toString = "%s.%s -> %s".format(rcvr, id, value)
}

/* Could extend CounterChunk */
case class IntCounterChunk(rcvr: Term, id: String, value: Int)
		extends PersistentChunk {

	def ++ = this + 1
	def +(n: Int) = this.copy(value = value + n)
	def -- = this - 1
	def -(n: Int) = this.copy(value = value - n)

	override def toString = "%s.%s -> %s".format(rcvr, id, value)
}

/*
 * Heap support
 */
 
// trait MapBasedFieldSupport[P <: Permission[P], S <: FieldSupport[P, S]]
		// extends FieldSupport[P, S] {

	// private lazy val fs: Map[(Term, String), FieldChunk[P]] =
		// (values
			// .collect { case c: FieldChunk[P] => c }
			// .map(c => ((c.rcvr, c.id), c)).toMap)
	
	// object FieldOperations extends super.FieldOperations {
		// def apply() = fs.values
		// def apply(rcvr: Term, id: String) = fs((rcvr, id))
		// def get(rcvr: Term, id: String) = fs.get((rcvr, id))
		// def value(rcvr: Term, id: String) = fs((rcvr, id)).value		
		
		// /* TODO: Throws an exception if rcvr.id is not present in fs */
		// def remove(rcvr: Term, id: String) =
			// from(values.filterNot(_ == fs((rcvr, id))))
			
		// def contains(rcvr: Term, id: String) = fs.contains((rcvr, id))
		
		// def update(c: FieldChunk[P]): S =
			// if (fs.contains((c.rcvr, c.id)))
				// from(values.filterNot(_ == fs((c.rcvr, c.id))) ++ (c :: Nil))
			// else
				// from(values ++ (c :: Nil))
	// }
	
	// val fields = FieldOperations
// }

// /* TODO: Share code between MapBasedFieldSupport and MapBasedPredicateSupport */
// trait MapBasedPredicateSupport[P <: Permission[P], S <: PredicateSupport[P, S]]
		// extends PredicateSupport[P, S] {

	// private lazy val ps: Map[(Term, String), PredicateChunk[P]] =
		// (values
			// .collect { case c: PredicateChunk[P] => c }
			// .map(c => ((c.rcvr, c.id), c)).toMap)
	
	// object PredicateOperations extends super.PredicateOperations {
		// def apply() = ps.values
		// def apply(rcvr: Term, id: String) = ps((rcvr, id))
		// def get(rcvr: Term, id: String) = ps.get((rcvr, id))
		// def snap(rcvr: Term, id: String) = ps((rcvr, id)).snap		
		
		// /* TODO: Throws an exception if rcvr.id is not present in fs */
		// def remove(rcvr: Term, id: String) =
			// from(values.filterNot(_ == ps((rcvr, id))))
			
		// def contains(rcvr: Term, id: String) = ps.contains((rcvr, id))
		
		// def update(c: PredicateChunk[P]): S =
			// if (ps.contains((c.rcvr, c.id)))
				// from(values.filterNot(_ == ps((c.rcvr, c.id))) ++ (c :: Nil))
			// else
				// from(values ++ (c :: Nil))
	// }
	
	// val predicates = PredicateOperations
// }