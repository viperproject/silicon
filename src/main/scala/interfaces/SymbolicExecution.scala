/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package interfaces

import silver.verifier.PartialVerificationError
import interfaces.state.Context
import state.{ChunkIdentifier, Store, Heap, State, Chunk}
import silicon.state.terms.{Sort, Term}

/*
 * Symbolic execution primitives
 */

trait Evaluator[ST <: Store[ST],
                H <: Heap[H],
								S <: State[ST, H, S],
                C <: Context[C]] {

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C)
					 (Q: (List[Term], C) => VerificationResult)
           : VerificationResult

	def eval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
					(Q: (Term, C) => VerificationResult)
          : VerificationResult

  def withChunkIdentifier(σ: S,
                          locacc: ast.LocationAccess,
                          assertRcvrNonNull: Boolean,
                          pve: PartialVerificationError,
                          c: C)
                         (Q: (ChunkIdentifier, C) => VerificationResult)
                         : VerificationResult
}

trait Producer[ST <: Store[ST],
               H <: Heap[H],
							 S <: State[ST, H, S],
               C <: Context[C]] {

	def produce(σ: S,
              sf: Sort => Term,
              p: Term,
              φ: ast.Expression,
              pve: PartialVerificationError,
              c: C)
						 (Q: (S, C) => VerificationResult)
             : VerificationResult

  def produces(σ: S,
               sf: Sort => Term,
               p: Term,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, C) => VerificationResult)
              : VerificationResult
}

trait Consumer[CH <: Chunk,
               ST <: Store[ST],
               H <: Heap[H],
							 S <: State[ST, H, S],
               C <: Context[C]] {

	def consume(σ: S, p: Term, φ: ast.Expression, pve: PartialVerificationError, c: C)
						 (Q: (S, Term, List[CH], C) => VerificationResult)
             : VerificationResult

  def consumes(σ: S,
               p: Term,
               φ: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[CH], C) => VerificationResult)
              : VerificationResult
}

trait Executor[X,
               ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C]] {

  def exec(σ: S,
           x: X,
           c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult
}
