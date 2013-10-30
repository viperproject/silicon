package semper
package silicon
package state

import interfaces.state.{Heap, Chunk, PermissionChunk, FieldChunk, PredicateChunk, ChunkIdentifier}
import terms.{Term, DefaultFractionalPermissions}

sealed trait DirectChunk extends PermissionChunk[DefaultFractionalPermissions, DirectChunk]

case class FieldChunkIdentifier(rcvr: Term, name: String) extends ChunkIdentifier {
  val args = rcvr :: Nil

  override def toString = s"$rcvr.$name"
}

case class DirectFieldChunk(rcvr: Term, name: String, value: Term, perm: DefaultFractionalPermissions)
    extends FieldChunk with DirectChunk {

  val args = rcvr :: Nil
  val id = FieldChunkIdentifier(rcvr, name)

	def +(perm: DefaultFractionalPermissions): DirectFieldChunk = this.copy(perm = this.perm + perm)
	def -(perm: DefaultFractionalPermissions): DirectFieldChunk = this.copy(perm = this.perm - perm)
  def \(perm: DefaultFractionalPermissions) = this.copy(perm = perm)

	override def toString = "%s.%s -> %s # %s".format(rcvr, name, value, perm)
}

case class PredicateChunkIdentifier(name: String, args: List[Term]) extends ChunkIdentifier {
  override def toString = "%s(%s)".format(name, args.mkString(","))
}

case class DirectPredicateChunk(name: String,
                                args: List[Term],
                                snap: Term,
                                perm: DefaultFractionalPermissions,
                                nested: List[NestedChunk] = Nil)
    extends PredicateChunk with DirectChunk {

  terms.utils.assertSort(snap, "snapshot", terms.sorts.Snap)

  val id = PredicateChunkIdentifier(name, args)

	def +(perm: DefaultFractionalPermissions): DirectPredicateChunk = this.copy(perm = this.perm + perm)
	def -(perm: DefaultFractionalPermissions): DirectPredicateChunk = this.copy(perm = this.perm - perm)
  def \(perm: DefaultFractionalPermissions) = this.copy(perm = perm)

	override def toString = "%s(%s;%s) # %s".format(name, args.mkString(","), snap, perm)
}


sealed trait NestedChunk extends Chunk

case class NestedFieldChunk(rcvr: Term, name: String, value: Term) extends FieldChunk with NestedChunk {
  val args = rcvr :: Nil
  val id = FieldChunkIdentifier(rcvr, name)

  def this(fc: DirectFieldChunk) = this(fc.rcvr, fc.name, fc.value)

  override def toString = "%s.%s -> %s".format(rcvr, name, value)
}

case class NestedPredicateChunk(name: String, args: List[Term], snap: Term, nested: List[NestedChunk] = Nil)
    extends PredicateChunk with NestedChunk {

  val id = PredicateChunkIdentifier(name, args)

  def this(pc: DirectPredicateChunk) = this(pc.name, pc.args, pc.snap, pc.nested)

  override def toString = "%s(%s;%s)".format(name, args.mkString(","), snap)
}


/* TODO: Chunk and ChunkIdentifier should be changed s.t. they don't require `name` and `args` anymore. */
case class MagicWandChunk[H <: Heap[H]](wandInstance: ast.MagicWand,
                                        localVariableTerms: Seq[Term],
                                        hPO: H) /* TODO: Do we want this to contribute to equals and hashCode? */
    extends DirectChunk {

  /* TODO: Big ugly hack! DirectChunk is extended so that DefaultConsumer can return a consumed
   *       MagicWandChunk in the list of consumed chunks. Apply(ing) needs the consumed chunk
   *       to get to the pold-heap which is needed while consuming the rhs of the wand-to-apply.
   */
  val perm = terms.NoPerm()
  def +(perm: DefaultFractionalPermissions) = sys.error("Unexpected call")
  def -(perm: DefaultFractionalPermissions) = sys.error("Unexpected call")
  def \(perm: DefaultFractionalPermissions) = sys.error("Unexpected call")

  val name = MagicWandChunkUtils.name(wandInstance)
  val args = localVariableTerms
  def id = MagicWandChunkIdentifier(wandInstance, localVariableTerms)

  override val toString = s"$name(${wandInstance.pos}, ${localVariableTerms.mkString("[", ", ", "]")}, $hPO)"
}

case class MagicWandChunkIdentifier(wandInstance: ast.MagicWand, localVariableTerms: Seq[Term]) extends ChunkIdentifier {
  val name = MagicWandChunkUtils.name(wandInstance)
  val args = localVariableTerms
}

private object MagicWandChunkUtils {
  def name(wand: ast.MagicWand) = "$MagicWandChunk" + wand.hashCode /* TODO: Hack! Equality should be used to compare wands syntactically! */
}
