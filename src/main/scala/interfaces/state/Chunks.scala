package semper
package silicon
package interfaces.state

import state.terms.{Term, PermissionsTuple}

trait Chunk {
	def rcvr: Term
	def id: String
}
 
trait PermissionChunk extends Chunk {
  val perm: PermissionsTuple
  def +(perm: PermissionsTuple): PermissionChunk
  def -(perm: PermissionsTuple): PermissionChunk
}

trait FieldChunk extends Chunk {
  val value: Term
}

trait PredicateChunk extends Chunk {
  val snap: Term
}