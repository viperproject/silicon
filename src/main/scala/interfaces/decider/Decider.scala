package ch.ethz.inf.pm.silicon.interfaces.decider

import silAST.programs.symbols.{Function => SILFunction}

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term, Permissions, Var}
import silicon.interfaces.state.{Store, Heap, PathConditions, State,
		Chunk, FieldChunk, PredicateChunk}
import silicon.interfaces.VerificationResult
import silicon.interfaces.reporting.{Message}
// import silicon.ast

trait Decider[V, ST <: Store[V, ST], H <: Heap[H],
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
	def getFieldChunk(h: H, rcvr: Term, id: String): Option[FieldChunk]
	def getPredicateChunk(h: H, rcvr: Term, id: String): Option[PredicateChunk]

	def assertNoAccess(p: Permissions): Boolean
	def assertReadAccess(p: Permissions): Boolean
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean
	def assertWriteAccess(p: Permissions): Boolean
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean

	def isValidFraction(p: Permissions): Option[Message]
	def isNonNegativeFraction(p: Permissions): Boolean
	def isAsPermissive(perm: Permissions, other: Permissions): Boolean

	def fresh: Var
	def fresh(id: String): Var
	def fresh(v: V): Var
}