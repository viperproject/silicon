// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.{State, Store}
import viper.silicon.state.terms.Term

trait LetSupportRules extends SymbolicExecutionRules {
  def handle[E <: ast.Exp]
            (s: State, e: ast.Exp, pve: PartialVerificationError)
            (Q: (State, Store, E) => VerificationResult)
            : VerificationResult

  def handle[E <: ast.Exp]
            (s: State, let: ast.Let, pve: PartialVerificationError)
            (Q: (State, Store, E) => VerificationResult)
            : VerificationResult
}

object letSupporter extends LetSupportRules {
  import evaluator._

  def handle[E <: ast.Exp]
            (s: State, e: ast.Exp, pve: PartialVerificationError)
            (Q: (State, Store, E) => VerificationResult)
            : VerificationResult = {

    e match {
      case let: ast.Let => handle(s, Nil, let, pve)(Q)
      case _ => Q(s, Store(), e.asInstanceOf[E])
    }
  }

  def handle[E <: ast.Exp]
            (s: State, let: ast.Let, pve: PartialVerificationError)
            (Q: (State, Store, E) => VerificationResult)
            : VerificationResult = {

    handle(s, Nil, let, pve)(Q)
  }

  private def handle[E <: ast.Exp]
                    (s: State,
                     bindings: Seq[(ast.AbstractLocalVar, (Term, Option[ast.Exp]))],
                     let: ast.Let,
                     pve: PartialVerificationError)
                    (Q: (State, Store, E) => VerificationResult)
                    : VerificationResult = {

    val ast.Let(x, exp, body) = let

    eval(s, exp, pve)((s1, t, expNew) => {
      val bindings1 = bindings :+ (x.localVar, (t, expNew))
      val s2 = s1.copy(s1.g + (x.localVar, (t, expNew)))
      body match {
        case nestedLet: ast.Let => handle(s2, bindings1, nestedLet, pve)(Q)
        case _ => Q(s2, Store(bindings1), body.asInstanceOf[E])}})
  }
}
