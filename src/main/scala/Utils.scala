package ch.ethz.inf.pm.silicon.utils

import scala.util.parsing.input.Positional
import com.weiglewilczek.slf4s.Logger
import ch.ethz.inf.pm.silicon
import silicon.reporting.{WarningMessages, ErrorMessages}
// import silicon.ASTConversionException

/*
object exceptions {
	def formatMessage(msg: Any): String = msg match {
		case prod: Product => prod.productPrefix
		case other => other.toString
	}
	
	def warnSupport(logger: Logger, loc: Positional, msg: String) =
		logger.debug(
			WarningMessages.NotSupported.withDetails(msg).at(loc.pos).format)

	def abortUnsupported(loc: Positional, details: String = "") = {
		val err = (ErrorMessages.NotSupported
								at loc.pos
								withDetails (formatMessage(loc)) + details)

		throw new ASTConversionException(err.code, err.format)
	}
}
*/

object collections {
	def mapReduceLeft[E](it: Iterable[E], f: E => E,
			op: (E, E) => E, unit: E): E =

		if (it.isEmpty)
			unit
		else
			it.map(f).reduceLeft((t1, t2) => op(t1, t2))
}