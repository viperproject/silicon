package semper
package silicon
package state

import interfaces.state.{Chunk, PermissionChunk, FieldChunk, PredicateChunk}
import terms.{Term, DefaultFractionalPermissions}

sealed trait DirectChunk extends PermissionChunk[DefaultFractionalPermissions, DirectChunk]

case class DirectFieldChunk(rcvr: Term, id: String, value: Term, perm: DefaultFractionalPermissions)
    extends FieldChunk with DirectChunk {

	def +(perm: DefaultFractionalPermissions): DirectFieldChunk = this.copy(perm = this.perm + perm)
	def -(perm: DefaultFractionalPermissions): DirectFieldChunk = this.copy(perm = this.perm - perm)

	override def toString = "%s.%s -> %s # %s".format(rcvr, id, value, perm)
}

case class DirectPredicateChunk(rcvr: Term,
                                id: String,
                                snap: Term,
                                perm: DefaultFractionalPermissions,
                                nested: List[NestedChunk] = Nil)
    extends PredicateChunk with DirectChunk {

  terms.utils.assertSort(snap, "snapshot", terms.sorts.Snap)

	def +(perm: DefaultFractionalPermissions): DirectPredicateChunk = this.copy(perm = this.perm + perm)
	def -(perm: DefaultFractionalPermissions): DirectPredicateChunk = this.copy(perm = this.perm - perm)

	override def toString = "%s.%s[%s] # %s".format(rcvr, id, snap, perm)
}


sealed trait NestedChunk extends Chunk

case class NestedFieldChunk(rcvr: Term, id: String, value: Term)
    extends FieldChunk with NestedChunk {

  def this(fc: DirectFieldChunk) = this(fc.rcvr, fc.id, fc.value)

  override def toString = "%s.%s -> %s".format(rcvr, id, value)
}

case class NestedPredicateChunk(rcvr: Term,
                                id: String,
                                snap: Term,
                                nested: List[NestedChunk] = Nil)
    extends PredicateChunk with NestedChunk {

  def this(pc: DirectPredicateChunk) = this(pc.rcvr, pc.id, pc.snap, pc.nested)

  override def toString = "%s.%s[%s]".format(rcvr, id, snap)
}
