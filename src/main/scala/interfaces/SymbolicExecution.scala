package semper
package silicon
package interfaces

import sil.verifier.{VerificationError, PartialVerificationError}
import state.{ChunkIdentifier, Store, Heap, State, Chunk}
import reporting.{Context, TraceView}
import silicon.state.terms.{Sort, Term, FractionalPermissions}

/*
 * Symbolic execution primitives
 */

trait Evaluator[P <: FractionalPermissions[P],
                ST <: Store[ST],
                H <: Heap[H],
								S <: State[ST, H, S],
                C <: Context[C, ST, H, S],
                TV <: TraceView[TV, ST, H, S]] {

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C, tv: TV)
					 (Q: (List[Term], C) => VerificationResult)
           : VerificationResult

	def eval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
					(Q: (Term, C) => VerificationResult)
          : VerificationResult

	def evalp(σ: S, p: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
					 (Q: (P, C) => VerificationResult)
           : VerificationResult

  def withChunkIdentifier(σ: S, memloc: ast.MemoryLocation, pve: PartialVerificationError, c: C, tv: TV)
                         (Q: (ChunkIdentifier, C) => VerificationResult)
                         : VerificationResult
}

trait Producer[P <: FractionalPermissions[P],
               ST <: Store[ST],
               H <: Heap[H],
							 S <: State[ST, H, S],
               C <: Context[C, ST, H, S],
               TV <: TraceView[TV, ST, H, S]] {

	def produce(σ: S,
              sf: Sort => Term,
              p: P,
              φ: ast.Expression,
              pve: PartialVerificationError,
              c: C,
              tv: TV)
						 (Q: (S, C) => VerificationResult)
             : VerificationResult

  def produces(σ: S,
               sf: Sort => Term,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, C) => VerificationResult)
              : VerificationResult
}

trait Consumer[P <: FractionalPermissions[P],
               CH <: Chunk,
               ST <: Store[ST],
               H <: Heap[H],
							 S <: State[ST, H, S],
               C <: Context[C, ST, H, S],
               TV <: TraceView[TV, ST, H, S]] {

	def consume(σ: S, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
						 (Q: (S, Term, List[CH], C) => VerificationResult)
             : VerificationResult

  def consumes(σ: S,
               p: P,
               φ: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, List[Term], List[CH], C) => VerificationResult)
              : VerificationResult
}

trait Executor[X,
               ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C, ST, H, S],
               TV <: TraceView[TV, ST, H, S]] {

  def exec(σ: S,
           x: X,
           c: C,
           tv: TV)
          (Q: (S, C) => VerificationResult)
          : VerificationResult
}
