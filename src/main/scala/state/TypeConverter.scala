package semper
package silicon
package state

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def manuallyHandledDomains: Set[ast.Domain]

  def toSort(typ: ast.DataType): Sort
}

class DefaultTypeConverter extends TypeConverter {
  val manuallyHandledDomains = Set(
    ast.types.Bool.domain,
    ast.types.Int.domain,
    ast.types.Perms.domain,
    ast.types.Ref.domain
  )

  def toSort(typ: ast.DataType) = typ match {
    case ast.types.Bool => sorts.Bool
    case ast.types.Int => sorts.Int
    case ast.types.Perms => sorts.Perms
    case ast.types.Ref => sorts.Ref
    case ast.types.NonRef(domain) => sorts.UserSort(domain.fullName)
  }
}