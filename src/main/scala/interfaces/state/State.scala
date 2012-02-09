package ch.ethz.inf.pm.silicon.interfaces.state

import ch.ethz.inf.pm.silicon
import silicon.state.terms.Term
// import silicon.ast.{Variable, IntType}

/* Conventions:
 *  - def \(...) should be intended to replace a component/an entry
 *  - def \+(...) should be intended to add or update it sth.
 */

/*
 * State components
 */
 
trait Store[V, S <: Store[V, S]] {
	def empty: S
	def values: Map[V, Term]
	def apply(key: V): Term
	def get(key: V): Option[Term]
	def +(kv: (V, Term)): S
	def +(other: S): S
}

trait Heap[S <: Heap[S]] {
	def empty: S
	def values: Iterable[Chunk]
	def +(chunk: Chunk): S
	def +(other: S): S
	def -(chunk: Chunk): S
}

trait PathConditions[S <: PathConditions[S]] {
	def empty: S
	def values: Set[Term]
	def contains(t: Term): Boolean
	def push(term: Term): S
	def pop(): S
	// def head: Term
	def pushScope(): S
	def popScope(): S
	// def headScope: Term[Set]
}

/*
 * State
 */

trait HasStore[V, ST <: Store[V, ST], S <: HasStore[V, ST, S]] {
	def γ: ST
	def \(γ: ST): S
	def \+(γ: ST): S
	def \+(v: V, t: Term): S
}

trait HasHeaps[H <: Heap[H], S <: HasHeaps[H, S]] {
	def h: H
	def g: H
	def \(h: H): S
	def \(h: H, g: H): S
	def \+(c: Chunk): S
	def \+(h: H): S
	def \-(c: Chunk): S
}

trait HasPathConditions {
	def π: Set[Term]
}

trait State[V, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]]
		extends HasStore[V, ST, S]
		with HasHeaps[H, S]
		with HasPathConditions {
	
	def \(γ: ST = γ, h: H = h, g: H = g): S
}

trait StateFormatter[V, ST <: Store[V, ST], H <: Heap[H],
										 S <: State[V, ST, H, S], F] {
	def format(σ: S): F
	def format(γ: ST): F
	def format(h: H): F
	def format(π: Set[Term]): F
}

trait HeapMerger[H <: Heap[H]] {
	def merge(h1: H, h2: H): (H, Set[Term])
}