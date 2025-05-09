// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.state

import viper.silicon.assumptionAnalysis.{AnalysisInfo, PermissionInhaleNode}
import viper.silicon.resources.ResourceID
import viper.silicon.state.terms.{Term, Var}
import viper.silver.ast

trait Chunk

trait ChunkIdentifer

trait GeneralChunk extends Chunk {
  val resourceID: ResourceID
  val id: ChunkIdentifer
  val perm: Term
  protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): GeneralChunk
  protected def permMinus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected def permPlus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]): GeneralChunk

  val permExp: Option[ast.Exp]
}

object GeneralChunk {
  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfo: AnalysisInfo): GeneralChunk = {
    val newChunk = chunk.applyCondition(newCond, newCondExp)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo): GeneralChunk = {
    val newChunk = chunk.permMinus(newPerm, newPermExp)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo): GeneralChunk = {
    val newChunk = chunk.permPlus(newPerm, newPermExp)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo): GeneralChunk = {
    val newChunk = chunk.withPerm(newPerm, newPermExp)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }
}

trait NonQuantifiedChunk extends GeneralChunk {
  val args: Seq[Term]
  val argsExp: Option[Seq[ast.Exp]]
  val snap: Term
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def permMinus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def permPlus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def withPerm(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  protected def withSnap(snap: Term, snapExp: Option[ast.Exp]): NonQuantifiedChunk
}

object NonQuantifiedChunk {
  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfo: AnalysisInfo): NonQuantifiedChunk = {
    val newChunk = chunk.withSnap(snap, snapExp)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }
}

trait QuantifiedChunk extends GeneralChunk {
  val quantifiedVars: Seq[Var]
  val quantifiedVarExps: Option[Seq[ast.LocalVarDecl]]

  def snapshotMap: Term
  def valueAt(arguments: Seq[Term]): Term
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): QuantifiedChunk
  override protected def permMinus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  override protected def permPlus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  protected def withSnapshotMap(snap: Term): QuantifiedChunk
}

object QuantifiedChunk {
  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfo: AnalysisInfo): QuantifiedChunk = {
    val newChunk = chunk.withSnapshotMap(snap)
    analysisInfo.getAssumptionAnalyzer.addPermissionDependencies(Set(chunk), PermissionInhaleNode(newChunk, analysisInfo.sourceInfo, analysisInfo.assumptionType))
    newChunk
  }
}