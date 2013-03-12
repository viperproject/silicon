package semper
package silicon
package state

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def manuallyHandledDomains: Seq[ast.Domain]

  def toSort(typ: ast.Type): Sort
}

class DefaultTypeConverter extends TypeConverter {
  val manuallyHandledDomains = Nil
//  Vector(
//    ast.types.Bool.domain,
//    ast.types.Int.domain,
//    ast.types.Perms.domain,
//    ast.types.Ref.domain
//  )

  def toSort(typ: ast.Type) = typ match {
    case ast.types.Bool => sorts.Bool
    case ast.types.Int => sorts.Int
    case ast.types.Perm => sorts.Perm
    case ast.types.Ref => sorts.Ref
//    case ast.types.NonRef(domain) => sorts.UserSort(domain.name)
    case dt: ast.types.DomainType =>
      assert(dt.isConcrete)
      sorts.UserSort(dt.domain.name)
    case sil.ast.Pred | _: sil.ast.TypeVar => ???
  }
}