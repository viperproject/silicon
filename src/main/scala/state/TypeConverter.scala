package ch.ethz.inf.pm.silicon
package state

import semper.sil.ast.types.{DataType => SILDataType}
import semper.sil.ast.domains.{Domain => SILDomain}

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def manuallyHandledDomains: Set[SILDomain]
  
	def toSort(typ: SILDataType): Sort
}

class DefaultTypeConverter extends TypeConverter {
  val manuallyHandledDomains = Set(
      semper.sil.ast.types.booleanType.domain,
      semper.sil.ast.types.integerType.domain,
      semper.sil.ast.types.permissionType.domain,
      semper.sil.ast.types.referenceType.domain
  )
  
	def toSort(typ: SILDataType) = typ match {
    case semper.sil.ast.types.booleanType => sorts.Bool
    case semper.sil.ast.types.integerType => sorts.Int
    case semper.sil.ast.types.permissionType => sorts.Perms
    case semper.sil.ast.types.referenceType => sorts.Ref
    case semper.sil.ast.types.NonReferenceDataType(domain) => sorts.UserSort(domain.fullName)
	}
}