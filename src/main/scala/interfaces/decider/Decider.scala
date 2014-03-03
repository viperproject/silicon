package semper
package silicon
package interfaces.decider

import sil.verifier.DependencyNotFoundError
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, ChunkIdentifier}
import interfaces.reporting.Context
import state.terms.{Term, Var, FractionalPermissions, Sort}
import silicon.utils.notNothing._

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

	def getChunk[CH <: Chunk: NotNothing: Manifest](h: H, id: ChunkIdentifier): Option[CH]

	def assertNoAccess(p: P): Boolean
	def assertReadAccess(p: P): Boolean
	def assertReadAccess(h: H, id: ChunkIdentifier): Boolean
	def assertWriteAccess(p: P): Boolean
	def assertWriteAccess(h: H, id: ChunkIdentifier): Boolean

	def isPositive(p: P, strict: Boolean = true): Boolean
	def isAsPermissive(perm: P, other: P): Boolean

  def fresh(s: Sort): Var
  def fresh(id: String, s: Sort): Var
	def fresh(v: ast.Variable): Var

  def start(): Option[DependencyNotFoundError]
  def stop()

  def getStatistics: Map[String, String]
}
