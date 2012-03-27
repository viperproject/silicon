package ch.ethz.inf.pm.silicon
package state

import silAST.types.{DataType => SILDataType}
// import silAST.types.{referenceType => SILReferenceType}
import silAST.domains.{Domain => SILDomain}

// import ch.ethz.inf.pm.silicon
import terms.{Sort, sorts}

/* TODO: Move to interfaces package */

/* TODO: Generalise file/package from TypeConverter to Types/Domains/something like that */

trait TypeConverter {
  def manuallyHandledDomains: Set[SILDomain]
  
	def toSort(typ: SILDataType): Sort
}

class DefaultTypeConverter extends TypeConverter {
	// def toSort(typ: SILDataType) = DataTypeSort(typ)
  
  val manuallyHandledDomains = Set(
      silAST.types.booleanType.domain,
      silAST.types.integerType.domain,
      silAST.types.permissionType.domain,
      silAST.types.referenceType.domain
  )
  
	def toSort(typ: SILDataType) = typ match {
		// case Type("bool", Nil) => BoolSort
		// case Type("int", Nil) => IntSort
		// // case Type("seq", List(_)) => SeqSort
		// case Type("seq", List(_)) => IntSort
		// // case Type("mu", Nil) => MuSort
		// case Type(_, Nil) => IntSort /* Any object reference */
    case silAST.types.booleanType => sorts.Bool
    case silAST.types.integerType => sorts.Int
    case silAST.types.permissionType => sorts.Perms
    case silAST.types.referenceType => sorts.Ref

    /* TODO: Generalise, specialisation to "real" bools should also happen in the 
     *       term converter.
     */
    // case silAST.types.NonReferenceDataType(_, domain) if domain.name == "Boolean[]" =>
      // sorts.Bool

    case silAST.types.NonReferenceDataType(_, domain) => sorts.UserSort(domain.fullName)
    
		// case _ => sys.error("Unsupported data type " + typ + ", " + typ.getClass.getName)
	}
}