/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common.collections.immutable

import scala.collection.{SetLike, mutable}
import scala.collection.generic.CanBuildFrom

class InsertionOrderedSet[E] private (protected val unorderedElements: Set[E],
                                      protected val orderedElements: Vector[E])
    extends Set[E] with SetLike[E, InsertionOrderedSet[E]] {

  def this() = this(Set.empty, Vector.empty)

  def contains(elem: E): Boolean = unorderedElements.contains(elem)

  def +(elem: E): InsertionOrderedSet[E] = {
    if (unorderedElements.contains(elem))
      this
    else {
      new InsertionOrderedSet(unorderedElements + elem, orderedElements :+ elem)
    }
  }

  def -(elem: E): InsertionOrderedSet[E] = {
    if (unorderedElements contains elem) {
      val newUnorderedElements = unorderedElements - elem

      /* TODO: More performant? Relies on orderedElements being duplicate-free */
//      val (before, elemAndAfter) = orderedElements.span(_ != elem)
//      val newOrderedElements = before ++ elemAndAfter.tail

      val newOrderedElements = orderedElements filterNot(_ == elem)

      new InsertionOrderedSet(newUnorderedElements, newOrderedElements)
    } else
      this
  }

  def iterator: Iterator[E] = orderedElements.iterator

  override def empty: InsertionOrderedSet[E] = InsertionOrderedSet.empty[E]
}

object InsertionOrderedSet {
  implicit def canBuildFrom[T] =
    new CanBuildFrom[InsertionOrderedSet[_], T, InsertionOrderedSet[T]] {
      def apply(from: InsertionOrderedSet[_]): mutable.Builder[T, InsertionOrderedSet[T]] =
        new mutable.Builder[T, InsertionOrderedSet[T]] {
          private var unorderedElems = Set.empty[T]  /* Must match type above */
          private var orderedElems = Vector.empty[T] /* Must match type above */

          def +=(elem: T) = {
            if (!(unorderedElems contains elem)) {
              unorderedElems = unorderedElems + elem
              orderedElems = orderedElems :+ elem
            }

            this
          }

          def clear() = {
            unorderedElems = Set.empty
            orderedElems = Vector.empty
          }

          def result() = new InsertionOrderedSet[T](unorderedElems, orderedElems)
       }

       def apply(): mutable.Builder[T, InsertionOrderedSet[T]] =
         apply(new InsertionOrderedSet())
    }

  def apply[E](): InsertionOrderedSet[E] = InsertionOrderedSet.empty

  def apply[E](elems: Iterable[E]): InsertionOrderedSet[E] = {
    new InsertionOrderedSet[E]() ++ elems
  }

//  def apply[E](elems: E*): InsertionOrderedSet[E] = {
//    new InsertionOrderedSet[E]() ++ elems
//  }

  def empty[E] = new InsertionOrderedSet[E]()
}
