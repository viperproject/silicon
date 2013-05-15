package semper
package silicon
package state

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def toSort(typ: ast.Type): Sort

  /* The suffixes T and S are only there because the methods would otherwise have the same
   * signature due to type erasure.
   */
  def toIdentifierT(base: String, types: Seq[ast.Type]): String
  def toIdentifierS(base: String, sorts: Seq[Sort]): String
}

class DefaultTypeConverter extends TypeConverter {
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

  def toIdentifierT(base: String, types: Seq[ast.Type]) = {
    val sorts = types map toSort
    toIdentifierS(base, sorts)
  }

  def toIdentifierS(base: String, sorts: Seq[Sort]) = {
    base + sorts.mkString("[",",","]")
  }
}
