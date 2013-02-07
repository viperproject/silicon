package semper
package silicon
package utils

object collections {
	def mapReduceLeft[E](it: Iterable[E], f: E => E, op: (E, E) => E, unit: E): E =
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