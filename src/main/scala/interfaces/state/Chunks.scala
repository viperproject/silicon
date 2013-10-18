package semper
package silicon
package interfaces.state

import state.terms.{Term, FractionalPermissions}

trait ChunkIdentifier {
  def name: String
  def args: List[Term]
}

trait Chunk {
  /* field name */
  def name: String
  def args: List[Term]
  def id: ChunkIdentifier
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
