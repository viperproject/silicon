/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon

package object utils {
	def mapReduceLeft[E](it: Iterable[E], f: E => E, op: (E, E) => E, unit: E): E =
		if (it.isEmpty)
			unit
		else
			it.map(f).reduceLeft((t1, t2) => op(t1, t2))

  /* Take from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
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

  object counter {
    private var value = 0

    def next() = {
      value = value + 1
      value
    }

    def reset() {
      value = 0
    }
  }
}
