/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import scala.collection.mutable
import viper.silver.ast
import viper.silicon.{Map, MSet, toSet}
import viper.silicon.interfaces.state.{Store, Heap, State, Chunk}
import viper.silicon.state.terms.Term

/*
 * Immutable implementation of the necessary state interfaces
 */

/*
 * State components
 */

case class MapBackedStore(private val map: Map[ast.AbstractLocalVar, Term])
    extends Store[MapBackedStore] {

  def this() = this(Map[ast.AbstractLocalVar, Term]())
  def this(pair: (ast.AbstractLocalVar, Term)) = this(Map(pair))

  val values = map
  def empty = new MapBackedStore()
  def apply(key: ast.AbstractLocalVar) = map(key)
  def get(key: ast.AbstractLocalVar) = map.get(key)
  def +(entry: (ast.AbstractLocalVar, Term)) = MapBackedStore(map + entry)
  def +(other: MapBackedStore) = MapBackedStore(map ++ other.map)
}

case class ListBackedHeap(private var chunks: List[Chunk]) extends Heap[ListBackedHeap] {
  def this() = this(Nil)
  def this(h: ListBackedHeap) = this(h.chunks)
  def this(chunks: Iterable[Chunk]) = this(chunks.toList)

  @inline
  def values = chunks

  /** Attention: This is a destructive operation that replaces the chunks in
    * this heap by `chunks`. Only use this operation if you think that you know
    * what you are doing! Consider creating a new heap via `this(chunks)`
    * instead.
    */
  def replace(chunks: Iterable[Chunk]) {
    this.chunks = chunks.toList
  }

  def empty = new ListBackedHeap()

  def +(ch: Chunk) = ListBackedHeap(chunks :+ ch)
  def +(h: ListBackedHeap) = new ListBackedHeap(h.chunks ::: chunks)

  def -(ch: Chunk) = new ListBackedHeap(chunks.filterNot(_ == ch))
}

/*
 * State
 */

case class DefaultState[ST <: Store[ST], H <: Heap[H]]
                       (γ: ST,
                        h: H,
                        g: H)
    extends State[ST, H, DefaultState[ST, H]] {

  def \(γ: ST) = this.copy(γ = γ)
  def \+(γ: ST) = this.copy(γ = this.γ + γ)
  def \+(v: ast.AbstractLocalVar, t: Term) = this.copy(γ = this.γ + (v, t))

  def \(h: H) = this.copy(h = h)
  def \(h: H, g: H) = this.copy(h = h, g = g)
  def \+(c: Chunk) = this.copy(h = this.h + c)
  def \+(h: H) = this.copy(h = this.h + h)
  def \-(c: Chunk) = this.copy(h = this.h - c)

  def \(γ: ST = γ, h: H = h, g: H = g) = this.copy(γ, h, g)
}
