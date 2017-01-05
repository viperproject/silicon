/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silicon.interfaces.state.Chunk

trait Heap {
  def values: Iterable[Chunk]
  def +(chunk: Chunk): Heap
  def +(other: Heap): Heap
  def -(chunk: Chunk): Heap
}

trait HeapFactory[H <: Heap] {
  def apply(): H
  def apply(chunks: Iterable[Chunk]): H
}

object Heap extends HeapFactory[ListBackedHeap] {
  def apply() = new ListBackedHeap(Vector.empty)
  def apply(chunks: Iterable[Chunk]) = new ListBackedHeap(chunks.toVector)
}

final class ListBackedHeap private[state] (chunks: Vector[Chunk])
    extends Heap with Immutable {

  def values = chunks

  def +(ch: Chunk) = new ListBackedHeap(chunks :+ ch)
  def +(h: Heap) = new ListBackedHeap(chunks ++ h.values)

  def -(ch: Chunk) = {
    val (prefix, suffix) = chunks.span(_ != ch)

    new ListBackedHeap(prefix ++ suffix.tail)
  }
}
