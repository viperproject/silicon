package ch.ethz.inf.pm.silicon
package state

import silAST.types.{DataType => SILDataType}
import silAST.domains.{Domain => SILDomain}

import terms.{Sort, sorts}

/* TODO: Move to interfaces package */
trait TypeConverter {
  def manuallyHandledDomains: Set[SILDomain]
  
	def toSort(typ: SILDataType): Sort
}

class DefaultTypeConverter extends TypeConverter {
  val manuallyHandledDomains = Set(
      silAST.types.booleanType.domain,
      silAST.types.integerType.domain,
      silAST.types.permissionType.domain,
      silAST.types.referenceType.domain
  )
  
	def toSort(typ: SILDataType) = typ match {
    case silAST.types.booleanType => sorts.Bool
    case silAST.types.integerType => sorts.Int
    case silAST.types.permissionType => sorts.Perms
    case silAST.types.referenceType => sorts.Ref
    case silAST.types.NonReferenceDataType(domain) => sorts.UserSort(domain.fullName)
	}
}