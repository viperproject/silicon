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
  def values: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])]
  def termValues: Map[ast.AbstractLocalVar, Term]
  def expValues: Map[ast.AbstractLocalVar, Option[ast.Exp]]
  def apply(key: ast.AbstractLocalVar): Term
  def get(key: ast.AbstractLocalVar): Option[Term]
  def getExp(key: ast.AbstractLocalVar): Option[ast.Exp]
  def +(kv: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))): Store
  def +(other: Store): Store
}

trait StoreFactory[ST <: Store] {
  def apply(): ST
  def apply(bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])]): ST
  def apply(pair: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))): ST
  def apply(pairs: Iterable[(ast.AbstractLocalVar, (Term, Option[ast.Exp]))]): ST
}

object Store extends StoreFactory[MapBackedStore] {
  def apply() = new MapBackedStore(Map.empty)
  def apply(pair: (AbstractLocalVar, (Term, Option[ast.Exp]))) = new MapBackedStore(Map(pair))
  def apply(bindings: Map[AbstractLocalVar, (Term, Option[ast.Exp])]) = new MapBackedStore(toMap(bindings))
  def apply(bindings: Iterable[(AbstractLocalVar, (Term, Option[ast.Exp]))]) = new MapBackedStore(toMap(bindings))
}

final class MapBackedStore private[state] (map: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])])
    extends Store {

  val values = map

  def termValues = values.map{case (localVar, pair) => localVar -> pair._1}
  def expValues = values.map{case (localVar, pair) => localVar -> pair._2}
  def apply(key: ast.AbstractLocalVar) = map(key)._1
  def get(key: ast.AbstractLocalVar) = termValues.get(key)
  def getExp(key: ast.AbstractLocalVar) = expValues.get(key) match {
    case Some(e) => e
    case None => None
  }
  def +(entry: (ast.AbstractLocalVar, (Term, Option[ast.Exp]))) = new MapBackedStore(map + entry)
  def +(other: Store) = new MapBackedStore(map ++ other.values)
}
