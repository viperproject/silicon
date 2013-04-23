package semper
package silicon
package interfaces.decider

import sil.verifier.{DependencyNotFoundError, ErrorReason}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk}
import interfaces.reporting.{Context}
import state.terms.{Term, Var, FractionalPermissions, Sort}
import utils.notNothing._

trait Decider[P <: FractionalPermissions[P], ST <: Store[ST], H <: Heap[H],
						PC <: PathConditions[PC], S <: State[ST, H, S], C <: Context[C, ST, H, S]] {

	def prover: Prover
	def π: Set[Term]

//	def enableSmokeChecks(enable: Boolean)
	def checkSmoke: Boolean

  def assert(φ: Term): Boolean
  def pushScope()
  def popScope()
  def inScope[R](block: => R): R
	def assume(φ: Term)
	def assume(φ: Set[Term])

	def getChunk[CH <: Chunk: NotNothing: Manifest](h: H, rcvr: Term, id: String): Option[CH]

	def assertNoAccess(p: P): Boolean
	def assertReadAccess(p: P): Boolean
	def assertReadAccess(h: H, rcvr: Term, id: String): Boolean
	def assertWriteAccess(p: P): Boolean
	def assertWriteAccess(h: H, rcvr: Term, id: String): Boolean

//	def isValidFraction(p: P, src: ast.Expression): Option[ErrorReason]
	def isPositive(p: P): Boolean
	def isAsPermissive(perm: P, other: P): Boolean

  def fresh(s: Sort): Var
  def fresh(id: String, s: Sort): Var
	def fresh(v: ast.Variable): Var

  def start(): Option[DependencyNotFoundError]
  def stop()

  def getStatistics: Map[String, String]
}
