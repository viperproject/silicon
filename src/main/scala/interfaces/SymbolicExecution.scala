package ch.ethz.inf.pm.silicon.interfaces

import silAST.expressions.terms.{LiteralTerm => SILLiteral}

import ch.ethz.inf.pm.silicon
import state.{Store, Heap, Permission, State}
import reporting.{Message}
import decider.Decider
import silicon.state.terms
import silicon.state.terms.{Term, Sort}
// import silicon.ast.{Expression, Statement, FractionalPermission}

/*
 * Symbolic execution components
 */

trait Evaluator[V, E, P <: Permission[P], ST <: Store[V, ST], H <: Heap[H],
								S <: State[V, ST, H, S]] {

	def evals(σ: S, es: List[E], m: Message,
						Q: (List[Term]) => VerificationResult): VerificationResult

	def eval(σ: S, e: E, m: Message,
					 Q: (Term) => VerificationResult): VerificationResult

	// def evalp(σ: S, p: FractionalPermission, m: Message,
					  // Q: P => VerificationResult): VerificationResult

	def evall(lit: SILLiteral): Term // terms.Literal
	// def evallm(lm: silicon.ast.LockMode): terms.LockMode
}

trait Producer[V, A, P <: Permission[P], ST <: Store[V, ST], H <: Heap[H],
							 S <: State[V, ST, H, S]] {

	def produce(σ: S, s: Term, p: P, φ: A, m: Message,
							Q: S => VerificationResult): VerificationResult
}

trait Consumer[V, A, P <: Permission[P], ST <: Store[V, ST], H <: Heap[H],
							 S <: State[V, ST, H, S]] {

	def consume(σ: S, p: P, φ: A, m: Message,
							Q: (S, Term) => VerificationResult): VerificationResult
}

trait Executor[V, STMT, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]] {

	def execs(σ: S, stmts: Seq[STMT], m: Message,
					 Q: S => VerificationResult): VerificationResult

	def exec(σ: S, stmt: STMT, m: Message,
					 Q: S => VerificationResult): VerificationResult
}

trait MapSupport[V, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]] {

	def getRevision(h: H, id: String): Int
	
	def update(σ: S, id: String, where: Term,
						 Q: S => VerificationResult): VerificationResult
}