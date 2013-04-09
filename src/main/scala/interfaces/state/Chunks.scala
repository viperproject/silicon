package semper
package silicon
package interfaces.state

import state.terms.{Term, FractionalPermissions}

trait Chunk {
	def rcvr: Term
	def id: String
}

trait PermissionChunk[P <: FractionalPermissions[P], CH <: PermissionChunk[P, CH]] extends Chunk {
  val perm: P
  def +(perm: P): CH
  def -(perm: P): CH
}

trait FieldChunk extends Chunk {
  val value: Term
}

trait PredicateChunk extends Chunk {
  val snap: Term
}
