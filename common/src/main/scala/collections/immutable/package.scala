// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.common.collections

import scala.collection.{IterableFactory, IterableFactoryDefaults}
import scala.collection.generic.DefaultSerializable
import scala.collection.immutable.{AbstractSet, ListSet, StrictOptimizedSetOps}

package object immutable {
  import scala.collection.mutable

  final case class InternalInsertionOrderedSet[E](s: mutable.LinkedHashSet[E]) extends AbstractSet[E]
    with StrictOptimizedSetOps[E, InternalInsertionOrderedSet, InternalInsertionOrderedSet[E]]  //TODO: double check
    with IterableFactoryDefaults[E, InternalInsertionOrderedSet] // TODO: double check
    with DefaultSerializable { // TODO: double check
    override def incl(elem: E): InternalInsertionOrderedSet[E] = {
      if (s.contains(elem)) {
        this
      } else {
        val ns = s.clone()
        val _ = ns.add(elem)
        InternalInsertionOrderedSet(ns)
      }
    }

    override def excl(elem: E): InternalInsertionOrderedSet[E] = {
      if (s.contains(elem)) {
        val ns = s.clone()
        val _ = ns.remove(elem)
        InternalInsertionOrderedSet(ns)
      } else {
        this
      }
    }

    override def contains(elem: E): Boolean = s.contains(elem)

    override def iterableFactory: IterableFactory[InternalInsertionOrderedSet] = ???

    override def iterator: Iterator[E] = s.iterator

    // overriding method not needed, but allows for optimization
    override def concat(that: IterableOnce[E]): InternalInsertionOrderedSet[E] = {
      if (that.iterator.nonEmpty) {
        val ns = s.clone()
        ns.addAll(that)
        InternalInsertionOrderedSet(ns)
      } else {
        this
      }
    }
  }

  case object InternalInsertionOrderedSet {
    def empty[E]: InternalInsertionOrderedSet[E] = InternalInsertionOrderedSet(mutable.LinkedHashSet.empty)
  }

  type InsertionOrderedSet[E] = InternalInsertionOrderedSet[E] // ListSet[E]

  object InsertionOrderedSet {
    def empty[E]: InsertionOrderedSet[E] = InternalInsertionOrderedSet.empty // ListSet.empty

    def apply[E](): InsertionOrderedSet[E] = InternalInsertionOrderedSet.empty // ListSet.empty
    def apply[E](e: E): InsertionOrderedSet[E] = InternalInsertionOrderedSet.empty + e // ListSet.empty + e
    def apply[E](es: InsertionOrderedSet[E]): InsertionOrderedSet[E] = es
    def apply[E](es: Iterable[E]): InsertionOrderedSet[E] = InternalInsertionOrderedSet.empty ++ es // ListSet.empty ++ es
  }

//  type InsertionOrderedSet[E] = Set[E]
//
//  object InsertionOrderedSet {
//    def empty[E]: InsertionOrderedSet[E] = Set.empty
//
//    def apply[E](): InsertionOrderedSet[E] = Set.empty
//    def apply[E](e: E): InsertionOrderedSet[E] = Set.empty + e
//    def apply[E](es: InsertionOrderedSet[E]): InsertionOrderedSet[E] = es
//    def apply[E](es: Iterable[E]): InsertionOrderedSet[E] = Set.empty ++ es
//  }
}
