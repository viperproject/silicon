/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import silver.ast
import interfaces.state.{Chunk, StoreFactory, HeapFactory, PathConditionsFactory, StateFactory}
import interfaces.state.factoryUtils.Ø
import state.terms.Term

trait DefaultStoreFactory extends StoreFactory[MapBackedStore] {
	def Γ() = new MapBackedStore()
	def Γ(pair: (ast.AbstractLocalVar, Term)) = new MapBackedStore(pair)
	def Γ(pairs: Iterable[(ast.AbstractLocalVar, Term)]) = new MapBackedStore(toMap(pairs))
	def Γ(store: Map[ast.AbstractLocalVar, Term]) = MapBackedStore(store)
}

trait DefaultHeapFactory extends HeapFactory[ListBackedHeap] {
	def H() = new ListBackedHeap()
	def H(h: ListBackedHeap) = new ListBackedHeap(h)
	def H(chunks: Iterable[Chunk]) = new ListBackedHeap(chunks)
}

class DefaultStateFactory
		(private val π: () => Set[Term])
		extends StateFactory[MapBackedStore, ListBackedHeap, DefaultState[MapBackedStore, ListBackedHeap]]
		with DefaultStoreFactory
		with DefaultHeapFactory {

	def Σ() = Σ(Ø, Ø, Ø)
	def Σ(γ: MapBackedStore, h: ListBackedHeap, g: ListBackedHeap) = DefaultState(γ, h, g, π)
}

class DefaultPathConditionsFactory
		extends PathConditionsFactory[MutableSetBackedPathConditions] {

	def Π() = new MutableSetBackedPathConditions()
	def Π(term: Term) = new MutableSetBackedPathConditions().push(term)

	def Π(terms: Set[Term]) = {
		val π = new MutableSetBackedPathConditions()
		terms foreach π.push
		π
	}
}
