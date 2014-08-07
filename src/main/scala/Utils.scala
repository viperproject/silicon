/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import reporting.DefaultContext
import state.terms._

package object utils {
	def mapReduceLeft[E](it: Iterable[E], f: E => E, op: (E, E) => E, unit: E): E =
		if (it.isEmpty)
			unit
		else
			it.map(f).reduceLeft((t1, t2) => op(t1, t2))

  /* Taken from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
  }

  def consumeExactRead(fp: Term, c: DefaultContext): Boolean = fp match {
    case _: WildcardPerm => false
    case v: Var => !c.constrainableARPs.contains(v)
    case TermPerm(t) => consumeExactRead(t, c)
    case PermPlus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermMinus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermTimes(t0, t1) => consumeExactRead(t0, c) && consumeExactRead(t1, c)
    case IntPermTimes(_, t1) => consumeExactRead(t1, c)
    case PermMin(t0 ,t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case Ite(_, t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case _ => true
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
