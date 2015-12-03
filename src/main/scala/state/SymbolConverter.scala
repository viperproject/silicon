/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import silver.ast
import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait SymbolConvert {
  def toSort(typ: ast.Type): Sort

  def toSortSpecificId(id: String, sorts: Seq[Sort]): String

  def toFunction(function: ast.DomainFunc): terms.Function
  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort]): terms.Function

  def toFunction(function: ast.Function): terms.Function
}

class DefaultSymbolConvert extends SymbolConvert {
  def toSort(typ: ast.Type) = typ match {
    case ast.Bool => sorts.Bool
    case ast.Int => sorts.Int
    case ast.Perm => sorts.Perm
    case ast.Ref => sorts.Ref

    case ast.SeqType(elementType) => sorts.Seq(toSort(elementType))
    case ast.SetType(elementType) => sorts.Set(toSort(elementType))
    case ast.MultisetType(elementType) => sorts.Multiset(toSort(elementType))

    case dt: ast.DomainType =>
      assert(dt.isConcrete, "Expected only concrete domain types, but found " + dt)
      sorts.UserSort(dt.toString())

    case   silver.ast.InternalType
         | _: silver.ast.TypeVar
         | silver.ast.Wand
         =>
      sys.error("Found unexpected type %s (%s)".format(typ, typ.getClass.getSimpleName))
  }

  def toSortSpecificId(id: String, sorts: Seq[Sort]) =
    id + sorts.mkString("[",",","]")

  def toFunction(function: ast.DomainFunc) = {
    val inSorts = function.formalArgs map (_.typ) map toSort
    val outSort = toSort(function.typ)

    toFunction(function, inSorts :+ outSort)
  }

  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort]) = {
    assert(sorts.nonEmpty, "Expected at least one sort, but found none")

    val inSorts = sorts.init
    val outSort = sorts.last
    val id = toSortSpecificId(function.name, sorts)

    terms.Function(id, inSorts, outSort)
  }

  def toFunction(function: ast.Function) = {
    val inSorts = terms.sorts.Snap +: (function.formalArgs map (_.typ) map toSort)
    val outSort = toSort(function.typ)

    terms.Function(function.name, inSorts, outSort)
  }
}
