package ch.ethz.inf.pm.silicon.interfaces

import silAST.expressions.terms.{LiteralTerm => SILLiteral}

import ch.ethz.inf.pm.silicon
import state.{Store, Heap, State}
import reporting.{Message}
import decider.Decider
import silicon.state.terms
import silicon.state.terms.{Term, Permissions, Sort}
// import silicon.ast.{Expression, Statement, FractionalPermission}

/*
 * Symbolic execution components
 */

trait Evaluator[V, E, T, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]] {
	def evales(σ: S, es: Seq[E], m: Message,
						Q: (List[Term]) => VerificationResult): VerificationResult
            
	def evalts(σ: S, es: Seq[T], m: Message,
						Q: (List[Term]) => VerificationResult): VerificationResult

	def evale(σ: S, e: E, m: Message,
					 Q: Term => VerificationResult): VerificationResult
           
	def evalt(σ: S, e: T, m: Message, Q: (Term) => VerificationResult): VerificationResult

	def evalp(σ: S, e: T, m: Message, Q: Permissions => VerificationResult)
           : VerificationResult

	// def evall(lit: SILLiteral): Term // terms.Literal
	// def evallm(lm: silicon.ast.LockMode): terms.LockMode
}

trait Producer[V, A, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]] {
	def produce(σ: S, s: Term, p: Permissions, φ: A, m: Message,
							Q: S => VerificationResult): VerificationResult
}

trait Consumer[V, A, ST <: Store[V, ST], H <: Heap[H], S <: State[V, ST, H, S]] {
	def consume(σ: S, p: Permissions, φ: A, m: Message,
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