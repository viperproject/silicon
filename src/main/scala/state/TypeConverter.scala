package semper
package silicon
package state

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def toSort(typ: ast.Type): Sort
}

class DefaultTypeConverter extends TypeConverter {
  def toSort(typ: ast.Type) = typ match {
    case ast.types.Bool => sorts.Bool
    case ast.types.Int => sorts.Int
    case ast.types.Perm => sorts.Perm
    case ast.types.Ref => sorts.Ref
//    case ast.types.NonRef(domain) => sorts.UserSort(domain.name)

    case dt: ast.types.DomainType =>
      assert(dt.isConcrete)
      sorts.UserSort(dt.domain.name)

    case sil.ast.Pred | _: sil.ast.TypeVar | _: ast.types.Seq => throw new MatchError(typ)
  }
}
