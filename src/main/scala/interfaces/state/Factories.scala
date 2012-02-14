package ch.ethz.inf.pm.silicon.interfaces.state

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term}
// import silicon.ast.Variable

object factoryUtils {
	trait Ø
	object Ø extends Ø
}

trait StoreFactory[V, ST <: Store[V, ST]] {
	implicit def ØToEmptyStore(ø: factoryUtils.Ø) = Γ()

	def Γ(): ST
	def Γ(store: Map[V, Term]): ST
	def Γ(pair: (V, Term)): ST
	def Γ(pairs: Iterable[(V, Term)]): ST
}

trait PathConditionsFactory[PC <: PathConditions[PC]] {
	implicit def ØToEmptyPathConditions(ø: factoryUtils.Ø) = Π()

	def Π(): PC
	def Π(terms: Term): PC
	def Π(terms: Set[Term]): PC
}

trait HeapFactory[H <: Heap[H]] {
	implicit def ØToEmptyHeap(ø: factoryUtils.Ø) = H()

	def H(): H
	def H(h: H): H
	def H(chunks: Iterable[Chunk]): H
}

trait StateFactory[V, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]]
		extends StoreFactory[V, ST] with HeapFactory[H] {

	implicit def ØToEmptyState(ø: factoryUtils.Ø) = Σ()

	def Σ(): S
	def Σ(γ: ST, h: H, g: H): S
}

// trait PermissionFactory[P <: Permission[P]] {
	// def Full: P
	// def Eps: P
// }