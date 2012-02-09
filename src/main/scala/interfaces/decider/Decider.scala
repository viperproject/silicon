package ch.ethz.inf.pm.silicon.interfaces.decider

import silAST.programs.symbols.{Function => SILFunction}

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term, Var, LockMode}
import silicon.interfaces.state.{Permission, Store, Heap, PathConditions, State,
		Chunk, FieldChunk, PredicateChunk}
import silicon.interfaces.VerificationResult
import silicon.interfaces.reporting.{Message}
// import silicon.ast

trait Decider[V, P <: Permission[P], ST <: Store[V, ST], H <: Heap[H],
							PC <: PathConditions[PC], S <: State[V, ST, H, S]] {

	def prover: Prover
	def π: Set[Term]

	/* TODO: Decouple Decider from ast.Function */
	def emitFunctionDeclaration(f: SILFunction)
	
	def enableSmokeChecks(enable: Boolean)
	def checkSmoke: Boolean

	def assert(φ: Term): Boolean
	def assume(term: Term, Q: => VerificationResult): VerificationResult
	
	def assume(term: Set[Term], Q: => VerificationResult)
						: VerificationResult

	def getChunk(h: H, rcvr: Term, id: String): Option[Chunk]
	def getFieldChunk(h: H, rcvr: Term, id: String): Option[FieldChunk[P]]
	def getPredicateChunk(h: H, rcvr: Term, id: String): Option[PredicateChunk[P]]

	def assertNoAccess(P: P): Boolean
	def assertReadAccess(P: P): Boolean
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean
	def assertWriteAccess(P: P): Boolean
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean

	def isValidFraction(P: P): Option[Message]
	def isNonNegativeFraction(P: P): Boolean
	def isAsPermissive(perm: P, other: P): Boolean

	def fresh: Var
	def fresh(id: String): Var
	def fresh(v: V): Var
}