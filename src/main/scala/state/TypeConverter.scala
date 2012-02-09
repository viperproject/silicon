package ch.ethz.inf.pm.silicon.state

import silAST.types.{DataType => SILDataType}

import silAST.types.{referenceType => SILReferenceType}

import ch.ethz.inf.pm.silicon
import terms.{Sort, RefSort /* BoolSort, IntSort, SeqSort, MuSort */ }
// import silicon.ast.Type
// import silicon.utils.exceptions.abortUnsupported

/* TODO: Move to interfaces package */
trait TypeConverter {
	def toSort(typ: SILDataType): terms.Sort
}

class DefaultTypeConverter extends TypeConverter {
	def toSort(typ: SILDataType) = typ match {
		// case Type("bool", Nil) => BoolSort
		// case Type("int", Nil) => IntSort
		// // case Type("seq", List(_)) => SeqSort
		// case Type("seq", List(_)) => IntSort
		// // case Type("mu", Nil) => MuSort
		// case Type(_, Nil) => IntSort /* Any object reference */
    case SILReferenceType => RefSort
		case _ => sys.error("Unsupported data type " + typ)
	}
}