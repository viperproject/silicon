/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state.terms

import scala.annotation.tailrec

sealed trait SolverResult {
  def readableMessage: String
}

case class PreSolvingError(msg: String) extends SolverResult {
  val readableMessage = msg
}

case class SolvingFailure(lhs: Term, rhs: Term, y: Var) extends SolverResult {
  val readableMessage = s"Solving for $y failed at $lhs == $rhs"
}

case class SolvingSuccess(y: Var, rhs: Term) extends SolverResult {
  val readableMessage = s"Solving succeeded with $y == $rhs"
}

object SimpleArithmeticTermSolver {
  def solve(lhs: Var, rhs: Term, y: Var): SolverResult = {
    if (lhs.sort != sorts.Int)
      return PreSolvingError(s"LHS must be of sort ${sorts.Int}, but found $lhs of sort ${lhs.sort}")
    else if (rhs.sort != sorts.Int)
      return PreSolvingError(s"RHS must be of sort ${sorts.Int}, but found $rhs of sort ${rhs.sort}")

    val rhsOccurrences = rhs.deepCollect{case `y` => y}.length

    if (lhs == y)
      PreSolvingError(s"The LHS must be different from $y")
    else if (rhsOccurrences != 1)
      PreSolvingError(s"$y must occur exactly once in the RHS, but it occurs $rhsOccurrences in $rhs")
    else {
      doSolve(lhs, rhs, y)
    }
  }

  @tailrec
  private def doSolve(lhs: Term, rhs: Term, y: Var): SolverResult = rhs match {
    case `y` => SolvingSuccess(y, lhs)
    case Plus(t1, t2) =>
      if (t1.contains(y)) doSolve(Minus(lhs, t2), t1, y)
      else doSolve(Minus(lhs, t1), t2, y)
    case Minus(t1, t2) =>
      if (t1.contains(y)) doSolve(Plus(lhs, t2), t1, y)
      else doSolve(Minus(t1, lhs), t2, y)
    case _ => SolvingFailure(lhs, rhs, y)
  }
}
