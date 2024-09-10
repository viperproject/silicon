// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.state

import viper.silicon.resources.ResourceID
import viper.silicon.state.terms.{Term, Var}
import viper.silver.ast

trait Chunk

trait ChunkIdentifer

trait GeneralChunk extends Chunk {
  val resourceID: ResourceID
  val id: ChunkIdentifer
  val perm: Term
  val permExp: Option[ast.Exp]

  def withPerm(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
}

trait NonQuantifiedChunk extends GeneralChunk {
  val args: Seq[Term]
  val argsExp: Option[Seq[ast.Exp]]
  val snap: Term
  override def withPerm(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  def withSnap(snap: Term): NonQuantifiedChunk
}

trait QuantifiedChunk extends GeneralChunk {
  val quantifiedVars: Seq[Var]
  val quantifiedVarExps: Option[Seq[ast.LocalVarDecl]]

  def snapshotMap: Term
  def valueAt(arguments: Seq[Term]): Term
  override def withPerm(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  def withSnapshotMap(snap: Term): QuantifiedChunk
}