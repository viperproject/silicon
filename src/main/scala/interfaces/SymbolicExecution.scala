/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.state.Context
import viper.silicon.interfaces.state.{Store, Heap, State, Chunk}
import viper.silicon.state.terms.{Sort, Term}

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
}

trait Producer[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

  def produce(σ: S,
              sf: Sort => Term,
              p: Term,
              φ: ast.Exp,
              pve: PartialVerificationError,
              c: C)
             (Q: (S, C) => VerificationResult)
             : VerificationResult

  def produces(σ: S,
               sf: Sort => Term,
               p: Term,
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

  def consume(σ: S, p: Term, φ: ast.Exp, pve: PartialVerificationError, c: C)
             (Q: (S, Term, C) => VerificationResult)
             : VerificationResult

  def consumes(σ: S,
               p: Term,
               φ: Seq[ast.Exp],
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
