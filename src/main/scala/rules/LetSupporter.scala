/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.{State, Store}
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier

trait LetSupportRules extends SymbolicExecutionRules {
  def handle[E <: ast.Exp]
            (s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
            (Q: (State, Store, E, Verifier) => VerificationResult)
            : VerificationResult

  def handle[E <: ast.Exp]
            (s: State, let: ast.Let, pve: PartialVerificationError, v: Verifier)
            (Q: (State, Store, E, Verifier) => VerificationResult)
            : VerificationResult
}

object letSupporter extends LetSupportRules with Immutable {
  import evaluator._

  def handle[E <: ast.Exp]
            (s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
            (Q: (State, Store, E, Verifier) => VerificationResult)
            : VerificationResult = {

    e match {
      case let: ast.Let => handle(s, Nil, let, pve, v)(Q)
      case _ => Q(s, Store(), e.asInstanceOf[E], v)
    }
  }

  def handle[E <: ast.Exp]
            (s: State, let: ast.Let, pve: PartialVerificationError, v: Verifier)
            (Q: (State, Store, E, Verifier) => VerificationResult)
            : VerificationResult = {

    handle(s, Nil, let, pve, v)(Q)
  }

  private def handle[E <: ast.Exp]
                    (s: State,
                     bindings: Seq[(ast.AbstractLocalVar, Term)],
                     let: ast.Let,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Store, E, Verifier) => VerificationResult)
                    : VerificationResult = {

    val ast.Let(x, exp, body) = let

    eval(s, exp, pve, v)((s1, t, v1) => {
      val bindings1 = bindings :+ (x.localVar, t)
      val s2 = s1.copy(s1.g + (x.localVar, t))
      body match {
        case nestedLet: ast.Let => handle(s2, bindings1, nestedLet, pve, v1)(Q)
        case _ => Q(s2, Store(bindings1), body.asInstanceOf[E], v1)}})
  }
}
