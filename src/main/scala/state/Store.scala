// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silicon.{Map, toMap}
import viper.silicon.state.terms.Term
import viper.silver.ast.AbstractLocalVar

trait Store {
  def values: Map[ast.AbstractLocalVar, Term]
  def apply(key: ast.AbstractLocalVar): Term
  def get(key: ast.AbstractLocalVar): Option[Term]
  def +(kv: (ast.AbstractLocalVar, Term)): Store
  def +(other: Store): Store
  def addEquality(t1: Term, t2: Term): Store
}

trait StoreFactory[ST <: Store] {
  def apply(): ST
  def apply(bindings: Map[ast.AbstractLocalVar, Term]): ST
  def apply(pair: (ast.AbstractLocalVar, Term)): ST
  def apply(pairs: Iterable[(ast.AbstractLocalVar, Term)]): ST
}

object Store extends StoreFactory[MapBackedStore] {
  def apply() = new MapBackedStore(Map.empty)
  def apply(pair: (AbstractLocalVar, Term)) = new MapBackedStore(Map(pair))
  def apply(bindings: Map[AbstractLocalVar, Term]) = new MapBackedStore(toMap(bindings))
  def apply(bindings: Iterable[(AbstractLocalVar, Term)]) = new MapBackedStore(toMap(bindings))
}

final class MapBackedStore private[state] (map: Map[ast.AbstractLocalVar, Term])
    extends Store {

  val values = map
  def apply(key: ast.AbstractLocalVar) = map(key)
  def get(key: ast.AbstractLocalVar) = map.get(key)
  def +(entry: (ast.AbstractLocalVar, Term)) = new MapBackedStore(map + entry)
  def +(other: Store) = new MapBackedStore(map ++ other.values)
  def addEquality(t1: Term, t2: Term) = {
    val newMap = map.map { case (k, v) => (k, v.replace(t1, t2)) }
    new MapBackedStore(newMap)
  }
}
