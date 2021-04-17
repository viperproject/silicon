// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.util

object Collections {
  /**
    * Returns all unordered pairs of the given elements.
    *
    * @param elements The elements.
    * @tparam T The type of the elements.
    * @return The pairs.
    */
  def pairs[T](elements: Iterable[T]): Iterable[(T, T)] =
    if (elements.isEmpty) Seq.empty
    else {
      val first = elements.head
      val rest = elements.tail
      rest.map { second => (first, second) } ++ pairs(rest)
    }

  def product[T](sets: Seq[Set[T]]): Set[Seq[T]] =
    sets match {
      case head +: tail => product(tail).flatMap { tuple => head.map { element => element +: tuple } }
      case _ => Set(Seq.empty)
    }
}

object SeqMap {
  @inline
  def add[K, V](map: Map[K, Seq[V]], key: K, element: V): Map[K, Seq[V]] =
    map.updated(key, map.get(key).map(_ :+ element).getOrElse(Seq(element)))

  def addAll[K, V](map: Map[K, Seq[V]], key: K, elements: Seq[V]): Map[K, Seq[V]] =
    map.updated(key, map.get(key).map(_ ++ elements).getOrElse(elements))
}

object SetMap {
  @inline
  def union[K, V](map1: Map[K, Set[V]], map2: Map[K, Set[V]]): Map[K, Set[V]] =
    map2.foldLeft(map1) { case (map, (key, value)) => addAll(map, key, value) }


  @inline
  def add[K, V](map: Map[K, Set[V]], key: K, element: V): Map[K, Set[V]] =
    map.updated(key, map.get(key).map(_ + element).getOrElse(Set(element)))

  @inline
  def addAll[K, V](map: Map[K, Set[V]], key: K, elements: Set[V]): Map[K, Set[V]] =
    map.updated(key, map.get(key).map(_ ++ elements).getOrElse(elements))
}
