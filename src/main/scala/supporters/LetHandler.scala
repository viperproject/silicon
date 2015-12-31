/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.{Evaluator, VerificationResult}
import viper.silicon.interfaces.state.{StateFactory, Context, State, Heap, Store}
import viper.silicon.state.terms.Term

trait LetHandler[ST <: Store[ST],
                 H <: Heap[H],
                 S <: State[ST, H, S],
                 C <: Context[C]] {

  def handle[E <: ast.Exp]
            (σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
            (Q: (ST, E, C) => VerificationResult)
            : VerificationResult

  def handle[E <: ast.Exp]
            (σ: S, let: ast.Let, pve: PartialVerificationError, c: C)
            (Q: (ST, E, C) => VerificationResult)
            : VerificationResult
}

trait DefaultLetHandler[ST <: Store[ST],
                        H <: Heap[H],
                        S <: State[ST, H, S],
                        C <: Context[C]]
    extends LetHandler[ST, H, S, C]
    { this: Evaluator[ST, H, S, C] =>

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  def handle[E <: ast.Exp]
            (σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
            (Q: (ST, E, C) => VerificationResult)
            : VerificationResult = {

    e match {
      case let: ast.Let => handle(σ, Nil, let, pve, c)(Q)
      case _ => Q(Γ(), e.asInstanceOf[E], c)
    }
  }

  def handle[E <: ast.Exp]
            (σ: S, let: ast.Let, pve: PartialVerificationError, c: C)
            (Q: (ST, E, C) => VerificationResult)
            : VerificationResult = {

    handle(σ, Nil, let, pve, c)(Q)
  }

  private def handle[E <: ast.Exp]
                    (σ: S,
                     bindings: Seq[(ast.AbstractLocalVar, Term)],
                     let: ast.Let,
                     pve: PartialVerificationError,
                     c: C)
                    (Q: (ST, E, C) => VerificationResult)
                    : VerificationResult = {

    val ast.Let(v, exp, body) = let

    eval(σ, exp, pve, c)((t, c1) => {
      val bindings1 = bindings :+ (v.localVar, t)
      val σ1 = σ \+ (v.localVar, t)
      body match {
        case nestedLet: ast.Let => handle(σ1, bindings1, nestedLet, pve, c1)(Q)
        case _ => Q(Γ(bindings1), body.asInstanceOf[E], c1)}})
  }
}
