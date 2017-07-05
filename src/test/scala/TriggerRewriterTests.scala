/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.tests

import java.io.{PrintWriter, StringWriter}
import org.scalatest.{FunSuite, Matchers}
import viper.silicon.state.Identifier
import DSL._
import viper.silicon.state.terms._

class TriggerRewriterTests extends FunSuite with Matchers {
  val dummySink = new PrintWriter(new StringWriter())
//  val dummyLogger = new MultiRunLogger(dummySink, () => None)
  val counter = new viper.silicon.utils.Counter()
  val triggerGenerator = new TriggerGenerator()

  val rewriter = new AxiomRewriter(counter/*, dummyLogger*/, triggerGenerator) {
    override def rewrite(quantification: Quantification) = {
      val result = super.rewrite(quantification)
      counter.reset()
      result
    }

    override protected def fresh(id: String, s: Sort): Var = {
      Var(Identifier(s"$id${counter.next()}"), s)
    }
  }

  val x0 = Var(Identifier("x0"), sorts.Int)
  val x1 = Var(Identifier("x1"), sorts.Int)
  val y0 = Var(Identifier("y0"), sorts.Int)
  val z0 = Var(Identifier("z0"), sorts.Int)

  import rewriter.rewrite

  test("No-ops") {
    val forall1 = Forall(x, True(), Trigger(f(x)), "forall1")
    val forall2 = Forall(x, f(x), Trigger(f(x)), "forall2")
    val forall3 = Forall(Seq(x, y, b), f(x), Trigger(f(x)), "forall3")

    rewrite(forall1) should be (Some(forall1))
    rewrite(forall2) should be (Some(forall2))
    rewrite(forall3) should be (Some(forall3))
  }

  test("Successes") {
    rewrite(
      Forall(x, x > `0`, Trigger(f(x + n)))
    ) should be (Some(
      Forall(x0, x0 - n > `0`, Trigger(f(x0)))
    ))

    rewrite(
      Forall(x, f(x, x + `1`) > x, Trigger(f(x, x + `1`)))
    ) should be (Some(
      Forall(Seq(x, x0), /* TODO: Make order of variables predictable (or use an ordered set) */
             (x === x0 - `1`) ==> (f(x, x0) > x),
             Trigger(f(x, x0)))
    ))

    rewrite(
      Forall(x, f(x + `1`) === g(x - `2`) + f(x), Trigger(Seq(f(x + `1`), g(x - `2`))))
    ) should be (Some(
      Forall(Seq(x0, x1),
             (x0 - `1` === x1 + `2`) ==> (f(x0) === g(x1) + f(x1 + `2`)),
              /* TODO: Replacing f(x) by f(x1 + `2`) is arbitrary, could as well
               *       be f(x + `1`). Can we make it the result more predictable?
               */
             Trigger(Seq(f(x0), g(x1))))
    ))

    rewrite(
      Forall(Seq(x, y, z), f(x, y + `1`) > z, Trigger(g(x, y + `1`, z)))
    ) should be (Some(
      Forall(Seq(x, z, y0), f(x, y0) > z, Trigger(g(x, y0, z)))
    ))
  }

  test("Failures") {
    rewrite(
      Forall(x, True(), Trigger(f(x * n)))
    ) should be (None) /* Multiplication is currently not handled */

    rewrite(
      Forall(x, True(), Trigger(f(x / n)))
    ) should be (None) /* Division is currently not handled */

    rewrite(
      Forall(Seq(x, y), True(), Trigger(f(x + y)))
    ) should be (None) /* Invalid triggers that mention more than one quantified variable are currently not handled */
  }
}
