/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import interfaces.state.{Chunk, PermissionChunk, FieldChunk, PredicateChunk, ChunkIdentifier}
import terms.{Lookup, Term, DefaultFractionalPermissions}
import state.terms.predef.`?r`

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

case class QuantifiedChunk(name: String, value: Term, perm: DefaultFractionalPermissions) extends Chunk {
  assert(value.sort.isInstanceOf[terms.sorts.FieldValueFunction],
         "Quantified chunk values must be of sort FieldValueFunction")

  val args = `?r` :: Nil
  val id = FieldChunkIdentifier(`?r`, name)

  def +(perm: DefaultFractionalPermissions): QuantifiedChunk = this.copy(perm = this.perm + perm)
  def -(perm: DefaultFractionalPermissions): QuantifiedChunk = this.copy(perm = this.perm - perm)

  def valueAt(rcvr: Term) = Lookup(name, value, rcvr)

  override def toString = "%s %s :: %s.%s -> %s # %s".format(terms.Forall, `?r`, `?r`, name, value, perm)
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
