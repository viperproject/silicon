package semper
package silicon
package interfaces.decider

import sil.verifier.ErrorReason
import interfaces.state.{Store, Heap, PathConditions, State, Chunk}
import interfaces.VerificationResult
import interfaces.reporting.{Context}
import state.terms.{Term, Var, PermissionsTerm, Sort}
import utils.notNothing._

trait Decider[P <: PermissionsTerm[P], ST <: Store[ST], H <: Heap[H],
						PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S]] {

	def prover: Prover
	def π: Set[Term]

//	def enableSmokeChecks(enable: Boolean)
//	def checkSmoke: Boolean

  def assert(φ: Term): Boolean
  def pushScope()
  def popScope()
  def inScope[R](block: => R): R
	def assume(φ: Term, c: C)
	def assume(φ: Set[Term], c: C)

	def getChunk[CH <: Chunk: NotNothing: Manifest](h: H, rcvr: Term, id: String): Option[CH]

	def assertNoAccess(p: P): Boolean
	def assertReadAccess(p: P): Boolean
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean
	def assertWriteAccess(p: P): Boolean
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean

	def isValidFraction(p: P, src: ast.Expression): Option[ErrorReason]
	def isNonNegativeFraction(p: P): Boolean
	def isAsPermissive(perm: P, other: P): Boolean

  def fresh(s: Sort): Var
  def fresh(id: String, s: Sort): Var
	def fresh(v: ast.Variable): Var

  def start()
  def stop()

  def getStatistics: Map[String, String]
}