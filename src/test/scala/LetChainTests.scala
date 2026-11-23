// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import java.nio.file.Files
import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
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

  /* Converts the term and checks that the names of shared subterms are only used where bound. */
  private def convert(t: Term): String = {
    val rendered = converter().convert(t)
    val tokens = rendered.replace("(", " ( ").replace(")", " ) ").split("\\s+").filter(_.nonEmpty).toList
    def parse(ts: List[String]): (Any, List[String]) = ts match {
      case "(" :: rest =>
        var items = List.empty[Any]
        var remaining = rest
        while (remaining.head != ")") {
          val (item, r) = parse(remaining)
          items ::= item
          remaining = r
        }
        (items.reverse, remaining.tail)
      case atom :: rest => (atom, rest)
      case Nil => fail(s"Unbalanced parentheses in $rendered")
    }
    def check(sexp: Any, bound: Set[String]): Unit = sexp match {
      case "let" :: (bindings: List[_]) :: body :: Nil =>
        val names = bindings.collect { case (name: String) :: value :: Nil => check(value, bound); name }
        check(body, bound ++ names)
      case items: List[_] => items.foreach(check(_, bound))
      case atom: String => assert(!atom.startsWith("$t@") || bound.contains(atom), s"$atom is not bound in $rendered")
    }
    check(parse(tokens)._1, Set.empty)
    rendered
  }

  test("Terms with a lot of sharing are rendered with lets") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val rendered = convert(BuiltinEquals(chain(60, x), IntLiteral(0)))
    assert(rendered.contains("(let"))
    assert(rendered.length < 10000)
  }

  test("Terms with a lot of sharing are rendered with lets inside quantifier bodies") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val body = BuiltinEquals(chain(60, x), IntLiteral(0))
    val rendered = convert(Forall(Seq(x), body, Seq(Trigger(Seq(Plus(x, x)))), "q"))
    assert(rendered.contains("(let"))
    assert(rendered.contains(":pattern"))
    assert(rendered.length < 10000)
  }

  test("Shared subterms are bound before they are used, even in parts of a term that are not among its subterms") {
    // MergeSingle's location is rendered, but is not among its subterms
    val x = Var(Identifier("x"), sorts.Int, false)
    val heap = Var(Identifier("h"), sorts.HeapSort(sorts.Int), false)
    val mask = Var(Identifier("m"), sorts.MaskSort, false)
    val shared = chain(20, x)
    val merged = MergeSingle(heap, mask, shared, x)
    val other = Var(Identifier("h2"), sorts.HeapSort(sorts.Int), false)
    val rendered = convert(And(BuiltinEquals(merged, other), BuiltinEquals(merged, heap), BuiltinEquals(shared, IntLiteral(0))))
    assert(rendered.contains("(let"))
  }

  test("Trigger terms with a lot of sharing are rendered with lets") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val y = Var(Identifier("y"), sorts.Int, false)
    val shared = chain(60, y)
    val rendered = convert(Forall(Seq(x), BuiltinEquals(Plus(x, shared), IntLiteral(0)), Seq(Trigger(Seq(Plus(x, shared)))), "q"))
    assert(rendered.contains(":pattern ((let"))
    assert(rendered.length < 10000)
  }

  test("Terms with little sharing are rendered without lets") {
    val x = Var(Identifier("x"), sorts.Int, false)
    val rendered = convert(BuiltinEquals(chain(3, x), IntLiteral(0)))
    assert(!rendered.contains("let"))
    assert(rendered.contains("(+ (+ (+ x x) (+ x x)) (+ (+ x x) (+ x x)))"))
  }

  test("Quantifiers with chains of lets are verified in reasonable time") {
    val n = 30

    def letChain(arg: String, body: String = s"p(a$n)"): String =
      s"let a0 == (q($arg)) in " +
        (1 to n).map(k => s"let a$k == (f(a${k - 1}, a${k - 1})) in ").mkString +
        body

    def seqLetChain(body: String): String =
      "let b0 == (s) in " +
        (1 to n).map(k => s"let b$k == (fs(b${k - 1}, b${k - 1})) in ").mkString +
        body

    val program =
      s"""field v: Int
         |function q(i: Int): Int
         |function f(a: Int, b: Int): Int
         |function p(i: Int): Bool
         |function h(i: Int, a: Int): Bool
         |function fs(a: Seq[Int], b: Seq[Int]): Seq[Int]
         |function gs(i: Int, a: Seq[Int]): Bool
         |function ks(b: Bool, a: Seq[Int]): Bool
         |function hs(i: Int): Bool
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
         |method assumeThenAssert()
         |  requires ${letChain("3")}
         |{ assert ${letChain("3")} }
         |
         |method triggerOutsideLet()
         |  requires ${letChain("0", s"(forall i: Int :: { h(i, a$n) } h(i, a$n))")}
         |{ assert ${letChain("0", s"h(5, a$n)")} }
         |
         |method seqInTrigger(s: Seq[Int])
         |  requires ${seqLetChain(s"(forall i: Int :: { i in s, gs(i, b$n) } (i in s && gs(i, b$n)) ==> hs(i))")}
         |  requires 5 in s
         |  requires ${seqLetChain(s"gs(5, b$n)")}
         |{ assert hs(5) }
         |
         |method seqInNestedTrigger(s: Seq[Int])
         |  requires ${seqLetChain(s"(forall i: Int :: { ks(i in s, b$n) } ks(i in s, b$n) ==> hs(i))")}
         |  requires ${seqLetChain(s"ks(5 in s, b$n)")}
         |{ assert hs(5) }
         |
         |method qpCondition(xs: Seq[Ref])
         |  requires forall i: Int, j: Int :: 0 <= i && i < j && j < |xs| ==> xs[i] != xs[j]
         |  requires ${letChain("0", s"(forall i: Int :: { xs[i] } 0 <= i && i < |xs| && p(a$n) ==> acc(xs[i].v))")}
         |{}
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
      /* Fail instead of hanging if verification takes exponential time (it should take seconds) */
      val result = Await.result(Future(tests.verifyProgram(frontend.translationResult, frontend)), 5.minutes)
      result match {
        case Failure(Seq(error: AssertFailed)) =>
          error.pos match {
            case pos: HasLineColumn =>
              val failLine = program.linesIterator.indexWhere(_.contains("assert !(")) + 1
              assert(pos.line == failLine, error) // The assertion in method fail
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
