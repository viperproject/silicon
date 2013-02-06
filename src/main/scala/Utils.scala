package semper
package silicon
package utils

import com.weiglewilczek.slf4s.Logger
//import reporting.{WarningMessages, ErrorMessages}

object exceptions {
	def formatMessage(msg: Any): String = msg match {
		case prod: Product => prod.productPrefix
		case other => other.toString
	}
	
//	def warnSupport(logger: Logger, loc: ast.SourceLocation, msg: String) =
//		logger.debug(
//			WarningMessages.NotSupported.withDetails(msg).at(loc).format)

	def abortUnsupported(node: ast.ASTNode, details: String = "") = {
    ???
//		val err = (
//      ErrorMessages.NotSupported at(node.sourceLocation)
//                                 withDetails(formatMessage(node) + details))
//
//    sys.error(err.format)
	}
}

object collections {
	def mapReduceLeft[E](it: Iterable[E], f: E => E,
			op: (E, E) => E, unit: E): E =

		if (it.isEmpty)
			unit
		else
			it.map(f).reduceLeft((t1, t2) => op(t1, t2))
}

/* http://www.tikalk.com/java/blog/avoiding-nothing */
object notNothing {
  sealed trait NotNothing[-T]

  object NotNothing {
    implicit object notNothing extends NotNothing[Any]

    implicit object `\n The error is because the type parameter was resolved to Nothing`
        extends NotNothing[Nothing]
  }
}