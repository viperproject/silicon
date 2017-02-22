/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common.collections.immutable

object MultiMap {
  /* Adapted from http://blog.xebia.com/multimap-in-scala/ */
  implicit class MultiMap[A, B](val map: Map[A, Set[B]]) extends AnyVal {
    def addBinding(key: A, value: B): Map[A, Set[B]] =
      map + (key -> (map.getOrElse(key, Set.empty) + value))

    def removeBinding(key: A, value: B): Map[A, Set[B]] = map.get(key) match {
      case None => map
      case Some(set) => map + (key -> (set - value))
    }
  }

  object MultiMap {
    def empty[A, B]: MultiMap[A, B] = new MultiMap(Map.empty)
  }
}