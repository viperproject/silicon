package semper
package silicon
package state

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait SymbolConvert {
  def toSort(typ: ast.Type): Sort

  def toSortSpecificId(id: String, sorts: Seq[Sort]): String

  def toFunction(function: ast.DomainFunction): terms.Function
  def toFunction(function: ast.DomainFunction, sorts: Seq[Sort]): terms.Function

  def toFunction(function: ast.ProgramFunction): terms.Function
}

class DefaultSymbolConvert extends SymbolConvert {
  def toSort(typ: ast.Type) = typ match {
    case ast.types.Bool => sorts.Bool
    case ast.types.Int => sorts.Int
    case ast.types.Perm => sorts.Perm
    case ast.types.Ref => sorts.Ref

    case dt: ast.types.DomainType =>
      assert(dt.isConcrete, "Expected only concrete domain types, but found " + dt)
      sorts.UserSort(dt.toString)

    case sil.ast.Pred | _: sil.ast.TypeVar | _: ast.types.Seq => throw new MatchError(typ)
  }

  def toSortSpecificId(id: String, sorts: Seq[Sort]) =
    id + sorts.mkString("[",",","]")

  def toFunction(function: ast.DomainFunction) = {
    val inSorts = function.formalArgs map (_.typ) map toSort
    val outSort = toSort(function.typ)

    toFunction(function, inSorts :+ outSort)
  }

  def toFunction(function: ast.DomainFunction, sorts: Seq[Sort]) = {
    assert(sorts.nonEmpty, "Expected at least one sort, but found none")

    val inSorts = sorts.init
    val outSort = sorts.last
    val id = toSortSpecificId(function.name, sorts)

    terms.Function(id, inSorts, outSort)
  }

  def toFunction(function: ast.ProgramFunction) = {
    val inSorts = terms.sorts.Snap +: (function.formalArgs map (_.typ) map toSort)
    val outSort = toSort(function.typ)

    terms.Function(function.name, inSorts, outSort)
  }
}
