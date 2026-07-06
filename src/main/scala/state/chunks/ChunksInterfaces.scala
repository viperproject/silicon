// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state.chunks

import viper.silicon
import viper.silicon.resources.ResourceID
import viper.silicon.state.terms.{Term, Var}
import viper.silver.ast

trait Chunk {
  val perm: Term
  val permExp: Option[ast.Exp]

  protected[chunks] def substitute(terms: silicon.Map[Term, Term]): Chunk
}

trait ChunkIdentifer

trait GeneralChunk extends Chunk {
  val resourceID: ResourceID
  val id: ChunkIdentifer

  protected[chunks] def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): GeneralChunk
  protected[chunks] def permMinus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected[chunks] def permPlus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected[chunks] def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]): GeneralChunk

  protected[chunks] def permScale(perm: Term, permExp: Option[ast.Exp]): GeneralChunk

  protected[chunks] def substitute(terms: silicon.Map[Term, Term]): GeneralChunk

  val permExp: Option[ast.Exp]
}

trait NonQuantifiedChunk extends GeneralChunk {
  val args: Seq[Term]
  val argsExp: Option[Seq[ast.Exp]]
  val snap: Term
  override protected[chunks] def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected[chunks] def permMinus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected[chunks] def permPlus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected[chunks] def withPerm(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  protected[chunks] def withSnap(snap: Term, snapExp: Option[ast.Exp]): NonQuantifiedChunk
}

trait QuantifiedChunk extends GeneralChunk {
  val quantifiedVars: Seq[Var]
  val quantifiedVarExps: Option[Seq[ast.LocalVarDecl]]
  def snapshotMap: Term
  def valueAt(arguments: Seq[Term]): Term
  override protected[chunks] def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): QuantifiedChunk
  override protected[chunks] def permMinus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  override protected[chunks] def permPlus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  protected[chunks] def withSnapshotMap(snap: Term): QuantifiedChunk
}
