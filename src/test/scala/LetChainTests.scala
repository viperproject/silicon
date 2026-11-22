// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.state.Identifier
import viper.silicon.state.terms._
import viper.silver.ast.HasLineColumn
import viper.silver.verifier.{Failure, Success}
import viper.silver.verifier.errors.AssertFailed

/** Terms are DAGs, e.g. a let-bound variable is replaced by the term of its value. Chains of lets
  * whose variables are used several times must therefore not be traversed or rendered as trees,
  * which takes exponential time.
  */
class LetChainTests extends AnyFunSuite {
  /* Also initialises the configuration needed to create terms */
  private val frontend = tests.instantiateFrontend()

  private def chain(n: Int, base: Term): Term =
    (1 to n).foldLeft(base)((t, _) => Plus(t, t))

  private def converter(): TermToSMTLib2Converter = {
    val c = new TermToSMTLib2Converter()
    c.start()
    c
  }

  test("Terms with a lot of sharing are rendered with lets") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val rendered = converter().convert(BuiltinEquals(chain(60, x), IntLiteral(0)))
    assert(rendered.contains("(let"))
    assert(rendered.length < 10000)
  }

  test("Terms with a lot of sharing are rendered with lets inside quantifier bodies") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val body = BuiltinEquals(chain(60, x), IntLiteral(0))
    val rendered = converter().convert(Forall(Seq(x), body, Seq(Trigger(Seq(Plus(x, x)))), "q"))
    assert(rendered.contains("(let"))
    assert(rendered.contains(":pattern"))
    assert(rendered.length < 10000)
  }

  test("Terms with little sharing are rendered as before, without lets") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val rendered = converter().convert(BuiltinEquals(chain(3, x), IntLiteral(0)))
    assert(!rendered.contains("let"))
    assert(rendered.contains("(+ (+ (+ x x) (+ x x)) (+ (+ x x) (+ x x)))"))
  }

  test("Quantifiers with chains of lets are verified in reasonable time") {
    val n = 30

    def letChain(arg: String): String =
      s"let a0 == (q($arg)) in " +
        (1 to n).map(k => s"let a$k == (f(a${k - 1}, a${k - 1})) in ").mkString +
        s"p(a$n)"

    val program =
      s"""function q(i: Int): Int
         |function f(a: Int, b: Int): Int
         |function p(i: Int): Bool
         |function g(i: Int): Bool { ${letChain("i")} }
         |
         |method instantiate()
         |  requires forall i: Int :: { q(i) } ${letChain("i")}
         |{ assert ${letChain("3")} }
         |
         |method check()
         |  requires forall i: Int :: { q(i) } ${letChain("i")}
         |  ensures forall i: Int :: { q(i) } ${letChain("i")}
         |{}
         |
         |method inFunction()
         |  requires forall i: Int :: { q(i) } g(i) && ${letChain("i")}
         |{ assert g(3) }
         |
         |method fail()
         |  requires forall i: Int :: { q(i) } ${letChain("i")}
         |{ assert !(${letChain("3")}) }
         |""".stripMargin

    val file = Files.createTempFile("letChain", ".vpr")
    try {
      Files.write(file, program.getBytes)
      frontend.reset(file)
      frontend.runTo(frontend.Translation)
      assert(frontend.errors.isEmpty, frontend.errors)
      tests.verifyProgram(frontend.translationResult, frontend) match {
        case Failure(Seq(error: AssertFailed)) =>
          error.pos match {
            case pos: HasLineColumn => assert(pos.line == 21, error) // The assertion in method fail
            case _ => fail(s"Unexpected position of $error")
          }
        case Failure(errors) => fail(s"Unexpected errors: $errors")
        case Success => fail("Expected the assertion in method fail to fail")
      }
    } finally {
      Files.delete(file)
    }
  }
}
