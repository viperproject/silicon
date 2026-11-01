// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.common.collections.immutable

import scala.collection.immutable.{AbstractSet, SetOps, StrictOptimizedSetOps, VectorMap}
import scala.collection.{IterableFactory, IterableFactoryDefaults, IterableOnce, mutable}

/** An immutable set that iterates over its elements in insertion order (as Scala's `ListSet`), but with
  * effectively constant-time `contains`, `incl` and `excl` (`ListSet` needs linear time for each of them).
  * Re-inserting an element that is already contained does not change its position.
  */
final class InsertionOrderedSet[E] private (private val elements: VectorMap[E, Unit])
    extends AbstractSet[E]
       with SetOps[E, InsertionOrderedSet, InsertionOrderedSet[E]]
       with StrictOptimizedSetOps[E, InsertionOrderedSet, InsertionOrderedSet[E]]
       with IterableFactoryDefaults[E, InsertionOrderedSet] {

  override def iterableFactory: IterableFactory[InsertionOrderedSet] = InsertionOrderedSet

  def contains(elem: E): Boolean = elements.contains(elem)

  def incl(elem: E): InsertionOrderedSet[E] =
    if (elements.contains(elem)) this
    else new InsertionOrderedSet(elements.updated(elem, ()))

  def excl(elem: E): InsertionOrderedSet[E] =
    if (elements.contains(elem)) new InsertionOrderedSet(elements.removed(elem))
    else this

  def iterator: Iterator[E] = elements.keysIterator

  override def size: Int = elements.size
  override def knownSize: Int = elements.size
  override def isEmpty: Boolean = elements.isEmpty

  override protected[this] def className: String = "InsertionOrderedSet"
}

object InsertionOrderedSet extends IterableFactory[InsertionOrderedSet] {
  private val emptySet = new InsertionOrderedSet[Any](VectorMap.empty)

  def empty[E]: InsertionOrderedSet[E] = emptySet.asInstanceOf[InsertionOrderedSet[E]]

  def from[E](source: IterableOnce[E]): InsertionOrderedSet[E] = source match {
    case set: InsertionOrderedSet[E @unchecked] => set
    case _ => (newBuilder[E] ++= source).result()
  }

  def newBuilder[E]: mutable.Builder[E, InsertionOrderedSet[E]] =
    new mutable.Builder[E, InsertionOrderedSet[E]] {
      private var elements = VectorMap.empty[E, Unit]

      def addOne(elem: E): this.type = {
        if (!elements.contains(elem)) elements = elements.updated(elem, ())
        this
      }

      def clear(): Unit = elements = VectorMap.empty

      def result(): InsertionOrderedSet[E] =
        if (elements.isEmpty) empty else new InsertionOrderedSet(elements)
    }

  def apply[E](): InsertionOrderedSet[E] = empty
  def apply[E](e: E): InsertionOrderedSet[E] = empty[E] + e
  def apply[E](es: InsertionOrderedSet[E]): InsertionOrderedSet[E] = es
  def apply[E](es: Iterable[E]): InsertionOrderedSet[E] = from(es)
}
