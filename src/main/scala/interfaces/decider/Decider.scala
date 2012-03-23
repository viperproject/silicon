package ch.ethz.inf.pm.silicon.interfaces.decider

import silAST.programs.symbols.{Function => SILFunction}
import silAST.domains.{Domain => SILDomain}

import ch.ethz.inf.pm.silicon
import silicon.state.terms.{Term, PermissionTerm, Var}
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
  def emitDomainDeclaration(d: SILDomain)
	
	def enableSmokeChecks(enable: Boolean)
	def checkSmoke: Boolean

	def assert(φ: Term): Boolean
	def assume(term: Term, Q: => VerificationResult): VerificationResult
	
	def assume(term: Set[Term], Q: => VerificationResult)
						: VerificationResult

	def getChunk(h: H, rcvr: Term, id: String): Option[Chunk]
	def getFieldChunk(h: H, rcvr: Term, id: String): Option[FieldChunk]
	def getPredicateChunk(h: H, rcvr: Term, id: String): Option[PredicateChunk]

	def assertNoAccess(p: PermissionTerm): Boolean
	def assertReadAccess(p: PermissionTerm): Boolean
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean
	def assertWriteAccess(p: PermissionTerm): Boolean
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean

	def isValidFraction(p: PermissionTerm): Option[Message]
	def isNonNegativeFraction(p: PermissionTerm): Boolean
	def isAsPermissive(perm: PermissionTerm, other: PermissionTerm): Boolean

	def fresh: Var
	def fresh(id: String): Var
	def fresh(v: V): Var
}