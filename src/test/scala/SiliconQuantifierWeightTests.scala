// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.state.DefaultSymbolConverter
import viper.silicon.state.terms.Term
import viper.silicon.supporters.ExpressionTranslator
import viper.silver.ast
import viper.silver.ast.{AnonymousDomainAxiom, Bool, Domain, DomainFunc, DomainFuncApp, EqCmp, Exists, Forall, Int, IntLit, LocalVar, LocalVarDecl, Method, Program, Seqn, Trigger, TrueLit, WeightedQuantifier}
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

class SiliconQuantifierWeightTests extends AnyFunSuite {
  val symbolConverter = new DefaultSymbolConverter()
  val termConverter = new TermToSMTLib2Converter()
  val translator = new ExpressionTranslator {
    def translateExpr(exp: ast.Exp): Term = {
      translate(symbolConverter.toSort)(exp)
    }
  }
  termConverter.start()

  val silicon: Silicon = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "QuantifierWeightTests") :: Nil
    new Silicon(reporter, debugInfo)
  }
  silicon.parseCommandLine(Seq("dummy.vpr"))
  silicon.start()

  test("The weight is part of the translation of a Forall") {
    val expr = Forall(
      Seq(LocalVarDecl("x", Int)()),
      Seq(),
      TrueLit()()
    )(
      info = WeightedQuantifier(12)
    )
    val term = translator.translateExpr(expr)
    val rendered = termConverter.convert(term)
    assert(rendered.contains(":weight 12"))
  }

  test("The weight is part of the translation of an Exists") {
    val expr = Exists(
      Seq(LocalVarDecl("x", Int)()),
      Seq(),
      TrueLit()()
    )(
      info = WeightedQuantifier(12)
    )
    val term = translator.translateExpr(expr)
    val rendered = termConverter.convert(term)
    assert(rendered.contains(":weight 12"))
  }

  test("The quantifier weight inhibits instantiations") {
    def verifyUsingWeight(weight: Int) = {
      val domainName = "MyDomain"
      val xDecl = LocalVarDecl("x", Int)()
      val x = LocalVar("x", Int)()
      val f = DomainFunc("f", Seq(xDecl), Int)(domainName = domainName)
      val singleApplication = DomainFuncApp(f, Seq(x), Map())()
      val nestedApplication = DomainFuncApp(f, Seq(DomainFuncApp(f, Seq(x), Map())()), Map())()
      val axiom = AnonymousDomainAxiom(Forall(
        Seq(xDecl),
        Seq(Trigger(Seq(singleApplication))()),
        EqCmp(nestedApplication, IntLit(42)())(),
      )(
        // Set the weight of the quantifier
        info = WeightedQuantifier(weight)
      ))(domainName = domainName)
      val domain = Domain(domainName, Seq(f), Seq(axiom))()
      val pre = EqCmp(singleApplication, IntLit(42)())()
      val post = EqCmp(nestedApplication, IntLit(42)())()
      val method = Method("test", Seq(LocalVarDecl("x", Int)()), Seq(), Seq(pre), Seq(post), Some(Seqn(Seq(), Seq())()))()
      val program = Program(Seq(domain), Seq(), Seq(), Seq(), Seq(method), Seq())()
      silicon.verify(program)
    }

    // A small weight should allow the axiom to be instantiated
    verifyUsingWeight(1) match {
      case Success => // Ok
      case Failure(errors) => assert(false)
    }

    // A big weight should prevent the axiom from being instantiated
    verifyUsingWeight(999) match {
      case Success => assert(false)
      case Failure(errors) => // Ok
    }
  }
}
