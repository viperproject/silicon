package semper
package silicon
package interfaces

import sil.verifier.{VerificationError, PartialVerificationError}
import state.{Store, Heap, State, Chunk}
import reporting.{Context, TraceView}
import silicon.state.terms.{Sort, Term, PermissionsTerm}

/*
 * Symbolic execution primitives
 */

trait Evaluator[P <: PermissionsTerm[P],
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
}

trait Producer[P <: PermissionsTerm[P],
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

trait Consumer[P <: PermissionsTerm[P],
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