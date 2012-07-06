package ch.ethz.inf.pm
package silicon
package interfaces
package decider

import silicon.state.terms.{Sort, Term, PermissionTerm, Var}
import state.{Store, Heap, PathConditions, State, Chunk, FieldChunk, PredicateChunk}
import reporting.{Message}

trait Decider[V, ST <: Store[V, ST], H <: Heap[H],
							PC <: PathConditions[PC], S <: State[V, ST, H, S]] {

	def prover: Prover
	def π: Set[Term]

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

  def fresh(s: Sort): Var
  def fresh(id: String, s: Sort): Var
  def fresh(v: V): Var
}