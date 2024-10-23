// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.state

import viper.silicon.resources.ResourceID
import viper.silicon.state.terms.{Term, Var}

trait Chunk

trait ChunkIdentifer

trait GeneralChunk extends Chunk {
  val resourceID: ResourceID
  val id: ChunkIdentifer
  val perm: Term
  def applyCondition(newCond: Term): GeneralChunk
  def permMinus(perm: Term): GeneralChunk
  def permPlus(perm: Term): GeneralChunk
}

trait NonQuantifiedChunk extends GeneralChunk {
  val args: Seq[Term]
  val snap: Term

  override def applyCondition(newCond: Term): NonQuantifiedChunk
  override def permMinus(perm: Term): NonQuantifiedChunk
  override def permPlus(perm: Term): NonQuantifiedChunk
  def withPerm(perm: Term): NonQuantifiedChunk
  def withArgs(args: Seq[Term]): NonQuantifiedChunk
  def withSnap(snap: Term): NonQuantifiedChunk
}

trait QuantifiedChunk extends GeneralChunk {
  val quantifiedVars: Seq[Var]
  def snapshotMap: Term
  def valueAt(arguments: Seq[Term]): Term

  override def applyCondition(newCond: Term): QuantifiedChunk
  override def permMinus(perm: Term): QuantifiedChunk
  override def permPlus(perm: Term): QuantifiedChunk
  def withSnapshotMap(snap: Term): QuantifiedChunk
}