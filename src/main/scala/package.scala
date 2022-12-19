// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper

import scala.language.implicitConversions

package object silicon {
  type TriggerSet[T] = Seq[T]
  type TriggerSets[T] = Seq[TriggerSet[T]]

  /* Immutable collections with a deterministic iteration order */

  type Map[K, +V] = scala.collection.immutable.TreeSeqMap[K, V]
  val Map = scala.collection.immutable.TreeSeqMap

  @inline
  def toMap[K, V](it: Iterable[(K, V)]): Map[K, V] = Map.empty ++ it

  type Stack[+E] = Seq[E]
  val Stack = List

  /* Mutable collections with a deterministic iteration order */

  type MList[A] = collection.mutable.ListBuffer[A]
  val MList = collection.mutable.ListBuffer

  type MSet[A] = collection.mutable.LinkedHashSet[A]
  val MSet = collection.mutable.LinkedHashSet

  type MMap[K, V] = collection.mutable.LinkedHashMap[K, V]
  val MMap = collection.mutable.LinkedHashMap

  type MStack[A] = collection.immutable.List[A]
  val MStack = collection.immutable.List

  /* Implicits converting from Predef.Map/Set to the Map/Set types defined above */

  object implicits {
    @inline
    implicit def predefMapToMap[K, V](map: Predef.Map[K, V]): Map[K, V] = Map.empty ++ map
  }
}
