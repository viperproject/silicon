/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.ast
import viper.silicon.{Map, toMap, Set}
import viper.silicon.interfaces.state.{Chunk, StoreFactory, HeapFactory, StateFactory}
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.state.terms.Term

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

class DefaultStateFactory()
    extends StateFactory[MapBackedStore, ListBackedHeap, DefaultState[MapBackedStore, ListBackedHeap]]
    with DefaultStoreFactory
    with DefaultHeapFactory {

  def Σ() = Σ(Ø, Ø, Ø)
  def Σ(γ: MapBackedStore, h: ListBackedHeap, g: ListBackedHeap) = DefaultState(γ, h, g)
}
