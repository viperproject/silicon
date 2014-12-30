/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import silver.ast
import interfaces.state.{Chunk, PermissionChunk, FieldChunk, PredicateChunk, ChunkIdentifier}
import terms.{PermMinus, PermPlus, Term}

sealed trait DirectChunk extends PermissionChunk[DirectChunk]

case class FieldChunkIdentifier(rcvr: Term, name: String) extends ChunkIdentifier {
  val args = rcvr :: Nil

  override def toString = s"$rcvr.$name"
}

case class DirectFieldChunk(rcvr: Term, name: String, value: Term, perm: Term)
    extends FieldChunk with DirectChunk {

  val args = rcvr :: Nil
  val id = FieldChunkIdentifier(rcvr, name)

  def +(perm: Term): DirectFieldChunk = this.copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): DirectFieldChunk = this.copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term) = this.copy(perm = perm)

  override def toString = "%s.%s -> %s # %s".format(rcvr, name, value, perm)
}

case class PredicateChunkIdentifier(name: String, args: List[Term]) extends ChunkIdentifier {
  override def toString = "%s(%s)".format(name, args.mkString(","))
}

case class DirectPredicateChunk(name: String,
                                args: List[Term],
                                snap: Term,
                                perm: Term,
                                nested: List[NestedChunk] = Nil)
    extends PredicateChunk with DirectChunk {

  val id = PredicateChunkIdentifier(name, args)

  def +(perm: Term): DirectPredicateChunk = this.copy(perm = PermPlus(this.perm, perm))
  def -(perm: Term): DirectPredicateChunk = this.copy(perm = PermMinus(this.perm, perm))
  def \(perm: Term) = this.copy(perm = perm)

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

abstract class MagicWandChunkLike extends {
  val ghostFreeWand: ast.MagicWand
  val evaluatedTerms: Seq[Term]
  val name = "$MagicWandChunk" + ghostFreeWand.hashCode /* TODO: Name just shouldn't be required for wand chunks */
  val args = Nil                                        /* TODO: Same for args */

  override lazy val toString = {
    val pos = ghostFreeWand.pos match {
      case rp: viper.silver.ast.RealPosition => s"${rp.line}:${rp.column}"
      case other => other.toString
    }

    s"wand@$pos[${evaluatedTerms.mkString(",")}]"
  }
}

case class MagicWandChunk(ghostFreeWand: ast.MagicWand, bindings: Map[ast.AbstractLocalVar, Term], evaluatedTerms: Seq[Term])
    extends MagicWandChunkLike with Chunk {

  lazy val id = MagicWandChunkIdentifier(ghostFreeWand, bindings, evaluatedTerms)
}

case class MagicWandChunkIdentifier(ghostFreeWand: ast.MagicWand, bindings: Map[ast.AbstractLocalVar, Term], evaluatedTerms: Seq[Term])
    extends MagicWandChunkLike with ChunkIdentifier {

  lazy val chunk = MagicWandChunk(ghostFreeWand, bindings, evaluatedTerms)
}
