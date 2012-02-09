package ch.ethz.inf.pm.silicon.state

import ch.ethz.inf.pm.silicon
import silicon.interfaces.state.{Store, Heap, PathConditions, State, Chunk, 
		Permission, StoreFactory, HeapFactory, PathConditionsFactory, StateFactory,
		PermissionFactory}
import silicon.interfaces.state.factoryUtils.Ø
// import silicon.ast.{Variable, Type, IntClass}
import silicon.state.terms.Term

trait DefaultStoreFactory[V] extends StoreFactory[V, MapBackedStore[V]] {
	def Γ() = new MapBackedStore()
	def Γ(pair: (V, Term)) = new MapBackedStore(pair)
	def Γ(pairs: Iterable[(V, Term)]) = new MapBackedStore(pairs.toMap)
	def Γ(store: Map[V, Term]) = MapBackedStore(store)
}

trait DefaultHeapFactory extends HeapFactory[MapBackedHeap] {
	def H() = new MapBackedHeap()
	def H(h: MapBackedHeap) = new MapBackedHeap(h)
	def H(chunks: Iterable[Chunk]) = new MapBackedHeap(chunks)
}

class DefaultStateFactory[V]
		(private val π: () => Set[Term])
		extends StateFactory[V, MapBackedStore[V], MapBackedHeap,
												 DefaultState[V, MapBackedStore[V], MapBackedHeap]]
		with DefaultStoreFactory[V]
		with DefaultHeapFactory {

	def Σ() = Σ(Ø, Ø, Ø)

	def Σ(γ: MapBackedStore[V], h: MapBackedHeap, g: MapBackedHeap) =
		DefaultState(γ, h, g, π)
}

class DefaultPermissionFactory extends PermissionFactory[FractionalPermission] {
	def Full = FullPerm
	def Eps = EpsPerm
}

class DefaultPathConditionsFactory
		extends PathConditionsFactory[MutableSetBackedPathConditions] {

	def Π() = new MutableSetBackedPathConditions()
	def Π(term: Term) = (new MutableSetBackedPathConditions()).push(term)
	
	def Π(terms: Set[Term]) = {
		val π = new MutableSetBackedPathConditions()
		terms foreach π.push
		π
	}
}