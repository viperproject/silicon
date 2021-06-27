// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.common.collections

import scala.collection.immutable.ListSet

package object immutable {
  type InsertionOrderedSet[E] = ListSet[E]

  object InsertionOrderedSet {
    def empty[E]: InsertionOrderedSet[E] = ListSet.empty

    def apply[E](): InsertionOrderedSet[E] = ListSet.empty
    def apply[E](e: E): InsertionOrderedSet[E] = ListSet.empty + e
    def apply[E](es: InsertionOrderedSet[E]): InsertionOrderedSet[E] = es
    def apply[E](es: Iterable[E]): InsertionOrderedSet[E] = ListSet.empty ++ es
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
