/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.ast
import viper.silicon.state.terms.{Sort, sorts}

trait SymbolConverter {
  def toSort(typ: ast.Type): Sort

  def toSortSpecificId(name: String, sorts: Seq[Sort]): Identifier

  def toFunction(function: ast.DomainFunc): terms.DomainFun
  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort]): terms.DomainFun

  def toFunction(function: ast.Function): terms.HeapDepFun
}

class DefaultSymbolConverter extends SymbolConverter with Immutable {
  def toSort(typ: ast.Type): Sort = typ match {
    case ast.Bool => sorts.Bool
    case ast.Int => sorts.Int
    case ast.Perm => sorts.Perm
    case ast.Ref => sorts.Ref

    case ast.SeqType(elementType) => sorts.Seq(toSort(elementType))
    case ast.SetType(elementType) => sorts.Set(toSort(elementType))
    case ast.MultisetType(elementType) => sorts.Multiset(toSort(elementType))

    case dt: ast.DomainType =>
      assert(dt.isConcrete, "Expected only concrete domain types, but found " + dt)
      sorts.UserSort(Identifier(dt.toString()))

    case   ast.InternalType
         | _: ast.TypeVar
         | ast.Wand
         =>
      sys.error("Found unexpected type %s (%s)".format(typ, typ.getClass.getSimpleName))
  }

  def toSortSpecificId(name: String, sorts: Seq[Sort]) =
    Identifier(name + sorts.mkString("[",",","]"))

  def toFunction(function: ast.DomainFunc): terms.DomainFun = {
    val inSorts = function.formalArgs map (_.typ) map toSort
    val outSort = toSort(function.typ)

    toFunction(function, inSorts :+ outSort)
  }

  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort]): terms.DomainFun = {
    assert(sorts.nonEmpty, "Expected at least one sort, but found none")

    val inSorts = sorts.init
    val outSort = sorts.last
    val id = Identifier(function.name)

    terms.DomainFun(id, inSorts, outSort)
  }

  def toFunction(function: ast.Function): terms.HeapDepFun = {
    val inSorts = terms.sorts.Snap +: (function.formalArgs map (_.typ) map toSort)
    val outSort = toSort(function.typ)

    terms.HeapDepFun(Identifier(function.name), inSorts, outSort)
  }
}
