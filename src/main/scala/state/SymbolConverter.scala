// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silicon.state.terms.{Sort, sorts}

trait SymbolConverter {
  def toSort(typ: ast.Type): Sort

  def toSortSpecificId(name: String, sorts: Seq[Sort]): Identifier

  def toFunction(function: ast.DomainFunc, prog: ast.Program): terms.Applicable
  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort], prog: ast.Program): terms.DomainFun

  def toFunction(function: ast.Function): terms.HeapDepFun
}

class DefaultSymbolConverter extends SymbolConverter {
  def toSort(typ: ast.Type): Sort = typ match {
    case ast.Bool => sorts.Bool
    case ast.Int => sorts.Int
    case ast.Perm => sorts.Perm
    case ast.Ref => sorts.Ref

    case ast.SeqType(elementType) => sorts.Seq(toSort(elementType))
    case ast.SetType(elementType) => sorts.Set(toSort(elementType))
    case ast.MultisetType(elementType) => sorts.Multiset(toSort(elementType))
    case ast.MapType(keyType, valueType) => sorts.Map(toSort(keyType), toSort(valueType))

    case dt: ast.DomainType =>
      assert(dt.isConcrete, "Expected only concrete domain types, but found " + dt)
      sorts.UserSort(Identifier(dt.toString()))

    case ast.BackendType(_, interpretations) if interpretations.contains("SMTLIB") => sorts.SMTSort(Identifier(interpretations("SMTLIB")))
    case ast.BackendType(_, _) => sys.error("Found backend type without SMTLIB name.")
    case viper.silicon.utils.ast.ViperEmbedding(sort) => sort
      
    case   ast.InternalType
         | _: ast.TypeVar
         | ast.Wand
         =>
      sys.error("Found unexpected type %s (%s)".format(typ, typ.getClass.getSimpleName))
  }

  def toSortSpecificId(name: String, sorts: Seq[Sort]): Identifier =
    Identifier(name + sorts.mkString("[",",","]"))

  def toFunction(function: ast.DomainFunc, program: ast.Program): terms.Applicable = {
    val inSorts = function.formalArgs map (_.typ) map toSort
    val outSort = toSort(function.typ)

    if (function.interpretation.isEmpty)
      toFunction(function, inSorts :+ outSort, program)
    else
      terms.SMTFun(Identifier(function.interpretation.get), inSorts, outSort)
  }

  def toFunction(function: ast.DomainFunc, sorts: Seq[Sort], program: ast.Program): terms.DomainFun = {
    assert(sorts.nonEmpty, "Expected at least one sort, but found none")

    val inSorts = sorts.init
    val outSort = sorts.last
    val domainFunc = program.findDomainFunctionOptionally(function.name)
    val id = if (domainFunc.isEmpty) Identifier(function.name) else toSortSpecificId(function.name, Seq(outSort))

    terms.DomainFun(id, inSorts, outSort)
  }

  def toFunction(function: ast.Function): terms.HeapDepFun = {
    val inSorts = terms.sorts.Snap +: (function.formalArgs map (_.typ) map toSort)
    val outSort = toSort(function.typ)

    terms.HeapDepFun(Identifier(function.name), inSorts, outSort)
  }
}
