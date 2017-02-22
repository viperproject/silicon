/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.common.collections.mutable

import scala.collection.mutable

/** Copy of scala.collection.mutable.MultiMap where all internally used
    * sets and maps have been replaced by those that guarantee a deterministic
    * traversal order.
    */
trait MMultiMap[A, B] extends mutable.LinkedHashMap[A, mutable.LinkedHashSet[B]] {
  def addBinding(key: A, value: B): this.type = {
    get(key) match {
      case None =>
        val set = new mutable.LinkedHashSet[B]()
        set += value
        this(key) = set
      case Some(set) =>
        set += value
    }
    this
  }

  def removeBinding(key: A, value: B): this.type = {
    get(key) match {
      case None =>
      case Some(set) =>
        set -= value
        if (set.isEmpty) this -= key
    }
    this
  }

  def entryExists(key: A, p: B => Boolean): Boolean = get(key) match {
    case None => false
    case Some(set) => set exists p
  }
}
