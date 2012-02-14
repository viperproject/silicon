package ch.ethz.inf.pm.silicon.state

import ch.ethz.inf.pm.silicon
import silicon.interfaces.state.{Heap, FieldChunk, PredicateChunk, Chunk,
    PersistentChunk}
import silicon.state.terms.{Term, Permissions, /* Token, */ Plus, PermPlus, Minus, PermMinus}

/*
 * Chunks
 */

/* TODO: Refactoring 'def +(perm: P)' and 'def -(perm: P)' 
 * 			 into an abstract base class seems
 *       to be non-straight-forward since 'copy' is a synthetic method
 *       added to case-classes by the compiler and not declared by any
 *       trait or interface.
 */

case class DefaultFieldChunk(rcvr: Term, id: String, value: Term, perm: Permissions)
    extends FieldChunk {
		
	def +(perm: Permissions) = this.copy(perm = PermPlus(this.perm, perm))
	def -(perm: Permissions) = this.copy(perm = PermMinus(this.perm, perm))
	
	override def toString = "%s.%s -> %s # %s".format(rcvr, id, value, perm)
}

case class DefaultPredicateChunk(rcvr: Term, id: String, snap: Term, perm: Permissions)
    extends PredicateChunk {
		
	def +(perm: Permissions) = this.copy(perm = PermPlus(this.perm, perm))
	def -(perm: Permissions) = this.copy(perm = PermMinus(this.perm, perm))
		
	override def toString = "%s.%s[%s] # %s".format(rcvr, id, snap, perm)
}

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