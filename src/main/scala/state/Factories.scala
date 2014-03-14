package semper
package silicon
package state

import interfaces.state.{Chunk, StoreFactory, HeapFactory, PathConditionsFactory, StateFactory}
import interfaces.state.factoryUtils.Ø
import state.terms.Term

trait DefaultStoreFactory extends StoreFactory[MapBackedStore] {
	def Γ() = new MapBackedStore()
	def Γ(pair: (ast.Variable, Term)) = new MapBackedStore(pair)
	def Γ(pairs: Iterable[(ast.Variable, Term)]) = new MapBackedStore(toMap(pairs))
	def Γ(store: Map[ast.Variable, Term]) = MapBackedStore(store)
}

trait DefaultHeapFactory extends HeapFactory[SetBackedHeap] {
	def H() = new SetBackedHeap()
	def H(h: SetBackedHeap) = new SetBackedHeap(h)
	def H(chunks: Iterable[Chunk]) = new SetBackedHeap(chunks)
}

class DefaultStateFactory
		(private val π: () => Set[Term])
		extends StateFactory[MapBackedStore, SetBackedHeap, DefaultState[MapBackedStore, SetBackedHeap]]
		with DefaultStoreFactory
		with DefaultHeapFactory {

	def Σ() = Σ(Ø, Ø, Ø)
	def Σ(γ: MapBackedStore, h: SetBackedHeap, g: SetBackedHeap) = DefaultState(γ, h, g, π)
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