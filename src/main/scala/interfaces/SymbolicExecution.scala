/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.state.Context
import viper.silicon.interfaces.state.{Store, Heap, State}
import viper.silicon.state.terms._

/*
 * Symbolic execution primitives
 */

trait Evaluator[ST <: Store[ST],
                H <: Heap[H],
                S <: State[ST, H, S],
                C <: Context[C]] {

  def evals(σ: S, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, c: C)
           (Q: (List[Term], C) => VerificationResult)
           : VerificationResult

  def eval(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult

  def evalLocationAccess(σ: S,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         c: C)
                        (Q: (String, Seq[Term], C) => VerificationResult)
                        : VerificationResult

  def evalQuantified(σ: S,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVar],
                     es1: Seq[ast.Exp],
                     es2: Seq[ast.Exp],
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     c: C)
                    (Q: (Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], Either[Quantification, Seq[Quantification]], C) => VerificationResult)
                    : VerificationResult
}

trait Producer[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

  /** Produce assertion φ into state σ.
    *
    * @param σ The state to produce the assertion into.
    * @param sf The heap snapshot determining the values of the produced partial heap.
    * @param φ The assertion to produce.
    * @param pve The error to report in case the production fails.
    * @param c The context to use.
    * @param Q The continuation to invoke if the production succeeded, with the state and context
    *          resulting from the production as arguments.
    * @return The result of the continuation.
    */
  def produce(σ: S,
              sf: Sort => Term,
              φ: ast.Exp,
              pve: PartialVerificationError,
              c: C)
             (Q: (S, C) => VerificationResult)
             : VerificationResult

  /** Subsequently produces assertions φs into state σ.
    *
    * `produces(σ, sf, φs, _ => pve, c)` should (not yet tested ...) be equivalent to
    * `produce(σ, sf, BigAnd(φs), pve, c)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param σ The state to produce the assertions into.
    * @param sf The heap snapshots determining the values of the produced partial heaps.
    * @param φs The assertions to produce.
    * @param pvef The error to report in case the production fails. Given assertions φs, an error
    *             pvef(φs_i) will be reported if producing assertion φs_i fails.
    * @param c @see [[produce]]
    * @param Q @see [[produce]]
    * @return @see [[produce]]
    */
  def produces(σ: S,
               sf: Sort => Term,
               φs: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               c: C)
              (Q: (S, C) => VerificationResult)
              : VerificationResult
}

trait Consumer[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

  /** Consume assertion φ from state σ.
    *
    * @param σ The state to consume the assertion from.
    * @param φ The assertion to consume.
    * @param pve The error to report in case the consumption fails.
    * @param c The context to use.
    * @param Q The continuation to invoke if the consumption succeeded, with the following
    *          arguments: state (1st argument) and context (3rd argument) resulting from the
    *          consumption, and a heap snapshot representing the values of the consumed partial
    *          heap.
    * @return The result of the continuation.
    */
  def consume(σ: S, φ: ast.Exp, pve: PartialVerificationError, c: C)
             (Q: (S, Term, C) => VerificationResult)
             : VerificationResult

  /** Subsequently consumes the assertions φs (from head to tail), starting in state σ.
    *
    * `consumes(σ, φs, _ => pve, c)` should (not yet tested ...) be equivalent to
    * `consume(σ, BigAnd(φs), pve, c)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param σ The state to consume the assertions from.
    * @param φs The assertions to consume.
    * @param pvef The error to report in case a consumption fails. Given assertions φs, an error
    *             pvef(φs_i) will be reported if consuming assertion φs_i fails.
    * @param c @see [[consume]]
    * @param Q @see [[consume]]
    * @return @see [[consume]]
    */
  def consumes(σ: S,
               φs: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               c: C)
              (Q: (S, Term, C) => VerificationResult)
              : VerificationResult
}

trait Executor[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

  def exec(σ: S,
           x: ast.Block,
           c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult

  def exec(σ: S, stmt: ast.Stmt, c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult

  def execs(σ: S, stmts: Seq[ast.Stmt], c: C)
           (Q: (S, C) => VerificationResult)
           : VerificationResult
}
