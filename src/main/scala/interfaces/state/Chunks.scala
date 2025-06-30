// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.state

import viper.silicon.assumptionAnalysis.{AnalysisInfo, AssumptionType, PermissionInhaleNode}
import viper.silicon.resources.ResourceID
import viper.silicon.state.terms.{PermMinus, Term, Var}
import viper.silver.ast

trait Chunk {
  val perm: Term
  val permExp: Option[ast.Exp]

  def getAnalysisInfo: String
}

trait ChunkIdentifer

trait GeneralChunk extends Chunk {
  val resourceID: ResourceID
  val id: ChunkIdentifer

  protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): GeneralChunk
  protected def permMinus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected def permPlus(perm: Term, permExp: Option[ast.Exp]): GeneralChunk
  protected def withPerm(newPerm: Term, newPermExp: Option[ast.Exp]): GeneralChunk
}

object GeneralChunk {
  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfo: AnalysisInfo): GeneralChunk = {
    analysisInfo.decider.registerDerivedChunk[GeneralChunk](chunk, {_ =>
      chunk.applyCondition(newCond, newCondExp)},
      chunk.perm, analysisInfo, isExhale=false, createLabel=false)
  }

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo, isExhale: Boolean=false): GeneralChunk = {
    val newChunk = analysisInfo.decider.registerDerivedChunk[GeneralChunk](chunk, {finalPerm =>
      chunk.permMinus(finalPerm, newPermExp)},
      newPerm, analysisInfo, isExhale=false, createLabel=false)
    val exhaledChunk = analysisInfo.decider.registerDerivedChunk[GeneralChunk](chunk, {finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfo, isExhale=true, createLabel=false)
    newChunk
  }

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo, isExhale: Boolean=false): GeneralChunk = {
    analysisInfo.decider.registerDerivedChunk[GeneralChunk](chunk, {finalPerm =>
      chunk.permPlus(finalPerm, newPermExp)},
      newPerm, analysisInfo, isExhale, createLabel=true)
  }

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfo: AnalysisInfo, isExhale: Boolean=false): GeneralChunk = {
    analysisInfo.decider.registerDerivedChunk[GeneralChunk](chunk, {finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfo, isExhale, createLabel=true)
  }
}

trait NonQuantifiedChunk extends GeneralChunk {
  val args: Seq[Term]
  val argsExp: Option[Seq[ast.Exp]]
  val snap: Term
  override def getAnalysisInfo: String = argsExp.getOrElse("") + " " + permExp.getOrElse("")
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def permMinus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def permPlus(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  override protected def withPerm(perm: Term, permExp: Option[ast.Exp]): NonQuantifiedChunk
  protected def withSnap(snap: Term, snapExp: Option[ast.Exp]): NonQuantifiedChunk
}

object NonQuantifiedChunk {
  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfo: AnalysisInfo): NonQuantifiedChunk = {
    analysisInfo.decider.registerDerivedChunk[NonQuantifiedChunk](chunk, {_ =>
      chunk.withSnap(snap, snapExp)},
      chunk.perm, analysisInfo, isExhale=false, createLabel=false)
  }
}

trait QuantifiedChunk extends GeneralChunk {
  val quantifiedVars: Seq[Var]
  val quantifiedVarExps: Option[Seq[ast.LocalVarDecl]]
  override def getAnalysisInfo: String = quantifiedVarExps.getOrElse("") + " " + permExp.getOrElse("")
  def snapshotMap: Term
  def valueAt(arguments: Seq[Term]): Term
  override protected def applyCondition(newCond: Term, newCondExp: Option[ast.Exp]): QuantifiedChunk
  override protected def permMinus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  override protected def permPlus(perm: Term, permExp: Option[ast.Exp]): QuantifiedChunk
  protected def withSnapshotMap(snap: Term): QuantifiedChunk
}

object QuantifiedChunk {
  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfo: AnalysisInfo): QuantifiedChunk = {
    analysisInfo.decider.registerDerivedChunk[QuantifiedChunk](chunk, {_ =>
      chunk.withSnapshotMap(snap)},
      chunk.perm, analysisInfo, isExhale=false, createLabel=false)
  }
}