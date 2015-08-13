/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package tests

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers
import state.terms._
import DSL._
import SimpleArithmeticTermSolver.solve

class SimpleArithmeticTermSolverTests extends FunSuite with ShouldMatchers {
  test("Pre-solving errors") {
    assert(solve(b, y, y).isInstanceOf[SolverResult])
    assert(solve(x, b, y).isInstanceOf[SolverResult])

    assert(solve(y, y, y).isInstanceOf[SolverResult])
    assert(solve(x, x, y).isInstanceOf[SolverResult])

    assert(solve(x, y + y, y).isInstanceOf[SolverResult])
  }

  test("Simple successes") {
    solve(x, y, y) should be (SolvingSuccess(y, x))
    solve(x, y + `1`, y) should be (SolvingSuccess(y, x - `1`))
    solve(x, n + y, y) should be (SolvingSuccess(y, x - n))
    solve(x, `0` - y, y) should be (SolvingSuccess(y, `0` - x))
    solve(x, y - x, y) should be (SolvingSuccess(y, x + x))
  }

  test("Simple failures") {
    solve(x, y + `1`, y) should not be SolvingSuccess(y, x + `1`)
    solve(x, `0` - y, y) should not be SolvingSuccess(y, x - `0`)
  }

  test("Successes") {
    solve(x, (`1` + y) - (n + x), y) should be (SolvingSuccess(y, x + (n + x) - `1`))
    solve(x, (y - f(x)) - f(m), y) should be (SolvingSuccess(y, x + f(m) + f(x)))
  }

  test("Failures") {
    solve(x, (n + f(y)) - m, y) should be (SolvingFailure(x + m - n, f(y), y))
  }
}

/* TODO: Add more operators/handy functions; make generally available */
private[tests] object DSL {
  implicit class ArithmeticOperators(t1: Term) {
    def +(t2: Term) = Plus(t1, t2)
    def -(t2: Term) = Minus(t1, t2)
    def *(t2: Term) = Times(t1, t2)
    def /(t2: Term) = Div(t1, t2)
    def >(t2: Term) = Greater(t1, t2)
  }

  implicit class BooleanOperators(t1: Term) {
    def &&(t2: Term) = And(t1, t2)
    def ==>(t2: Term) = Implies(t1, t2)
  }

  val x = Var("x", sorts.Int)
  val y = Var("y", sorts.Int)
  val z = Var("z", sorts.Int)
  val n = Var("n", sorts.Int)
  val m = Var("m", sorts.Int)
  val b = Var("b", sorts.Int)

  val `0` = IntLiteral(0)
  val `1` = IntLiteral(1)
  val `2` = IntLiteral(2)

  private val f1 = Var("f", sorts.Arrow(sorts.Int, sorts.Int))
  private val g1 = Var("g", sorts.Arrow(sorts.Int, sorts.Int))
  private val f2 = Var("f", sorts.Arrow(Seq(sorts.Int, sorts.Int), sorts.Int))
  private val g2 = Var("g", sorts.Arrow(Seq(sorts.Int, sorts.Int), sorts.Int))
  private val f3 = Var("f", sorts.Arrow(Seq(sorts.Int, sorts.Int, sorts.Int), sorts.Int))
  private val g3 = Var("g", sorts.Arrow(Seq(sorts.Int, sorts.Int, sorts.Int), sorts.Int))

  def f(t: Term) = Apply(f1, t :: Nil)
  def g(t: Term) = Apply(g1, t :: Nil)
  def f(t1: Term, t2: Term) = Apply(f2, t1 :: t2 :: Nil)
  def g(t1: Term, t2: Term) = Apply(g2, t1 :: t2 :: Nil)
  def f(t1: Term, t2: Term, t3: Term) = Apply(f2, t1 :: t2 :: t3 :: Nil)
  def g(t1: Term, t2: Term, t3: Term) = Apply(g2, t1 :: t2 :: t3 :: Nil)
}
