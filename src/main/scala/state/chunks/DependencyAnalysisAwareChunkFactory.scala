// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.state.chunks

import viper.silicon
import viper.silicon.decider.{Decider, DependencyAnalysisDeciderFeatures}
import viper.silicon.dependencyAnalysis.DependencyAnalysisInfos
import viper.silicon.resources.BaseID
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms.{MagicWandSnapshot, Term, Var}
import viper.silver.ast
import viper.silver.dependencyAnalysis.AssumptionType

import scala.annotation.unused

class DependencyAnalysisAwareChunkFactory(decider: Decider with DependencyAnalysisDeciderFeatures) extends ChunkFactory {
  override def createBasicChunk(resourceID: BaseID,
                                id: BasicChunkIdentifier,
                                args: Seq[Term],
                                argsExp: Option[Seq[ast.Exp]],
                                snap: Term,
                                snapExp: Option[ast.Exp],
                                perm: Term,
                                permExp: Option[ast.Exp],
                                analysisInfos: DependencyAnalysisInfos,
                                isExhale: Boolean = false): BasicChunk = {
    decider.registerChunk[BasicChunk]({finalPerm =>
      BasicChunk(resourceID, id, args, argsExp, snap, snapExp, finalPerm, permExp)
    },
      perm, analysisInfos, isExhale)
  }

  override def createQuantifiedFieldChunk(id: BasicChunkIdentifier,
                                          fvf: Term,
                                          condition: Term,
                                          conditionExp: Option[ast.Exp],
                                          permValue: Term,
                                          permValueExp: Option[ast.Exp],
                                          invs: Option[InverseFunctions],
                                          singletonRcvr: Option[Term],
                                          singletonRcvrExp: Option[ast.Exp],
                                          hints: Seq[Term] = Nil,
                                          analysisInfos: DependencyAnalysisInfos,
                                          isExhale: Boolean = false): QuantifiedFieldChunk = {
    decider.registerChunk[QuantifiedFieldChunk]({perm =>
      QuantifiedFieldChunk(id, fvf, condition, conditionExp, perm, permValueExp, invs, singletonRcvr, singletonRcvrExp, hints)
    },
      permValue, analysisInfos, isExhale)
  }

  override def createQuantifiedPredicateChunk(id: BasicChunkIdentifier,
                                              quantifiedVars: Seq[Var],
                                              quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                              psf: Term,
                                              condition: Term,
                                              conditionExp: Option[ast.Exp],
                                              permValue: Term,
                                              permValueExp: Option[ast.Exp],
                                              invs: Option[InverseFunctions],
                                              singletonArgs: Option[Seq[Term]],
                                              singletonArgExps: Option[Seq[ast.Exp]],
                                              hints: Seq[Term] = Nil,
                                              analysisInfos: DependencyAnalysisInfos,
                                              isExhale: Boolean = false): QuantifiedPredicateChunk = {
    decider.registerChunk[QuantifiedPredicateChunk]({ finalPerm =>
      QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, condition, conditionExp, finalPerm, permValueExp, invs, singletonArgs, singletonArgExps, hints)
    }, permValue, analysisInfos, isExhale)
  }

  override def createQuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                              quantifiedVars: Seq[Var],
                                              quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                              wsf: Term,
                                              perm: Term,
                                              permExp: Option[ast.Exp],
                                              invs: Option[InverseFunctions],
                                              singletonArgs: Option[Seq[Term]],
                                              singletonArgExps: Option[Seq[ast.Exp]],
                                              hints: Seq[Term] = Nil,
                                              analysisInfos: DependencyAnalysisInfos,
                                              isExhale: Boolean = false): QuantifiedMagicWandChunk = {
    decider.registerChunk[QuantifiedMagicWandChunk]({ finalPerm =>
      QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, finalPerm, permExp, invs, singletonArgs, singletonArgExps, hints)
    }, perm, analysisInfos, isExhale)
  }

  override def createMagicWandChunk(id: MagicWandIdentifier,
                                    bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                                    args: Seq[Term],
                                    argsExp: Option[Seq[ast.Exp]],
                                    snap: MagicWandSnapshot,
                                    perm: Term,
                                    permExp: Option[ast.Exp],
                                    analysisInfos: DependencyAnalysisInfos,
                                    isExhale: Boolean = false): MagicWandChunk = {
    decider.registerChunk[MagicWandChunk]({ finalPerm =>
      MagicWandChunk(id, bindings, args, argsExp, snap, finalPerm, permExp)
    }, perm, analysisInfos, isExhale)
  }

  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk = {
    decider.registerDerivedChunk(Set(chunk), {_ =>
      chunk.applyCondition(newCond, newCondExp)},
      chunk.perm, analysisInfos, isExhale=false, createLabel=false)
  }

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): GeneralChunk = {
    val newChunk = decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.permMinus(finalPerm, newPermExp)},
      newPerm, analysisInfos.withDependencyType(AssumptionType.Internal), isExhale=false, createLabel=false) // TODO ake: assumption type? maybe for exhale we want to have Implicit?
    @unused // we need to register the chunk to have a sound analysis
    val exhaledChunk = decider.registerDerivedChunk(Set(chunk), { finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale=true, createLabel=false)
    newChunk
  }

  def permMinus(chunk: QuantifiedBasicChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): QuantifiedBasicChunk = {
    val newChunk = decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.permMinus(finalPerm, newPermExp)},
      newPerm, analysisInfos.withDependencyType(AssumptionType.Internal), isExhale=false, createLabel=false) // TODO ake: assumption type? maybe for exhale we want to have Implicit?
    @unused // we need to register the chunk to have a sound analysis
    val exhaledChunk = decider.registerDerivedChunk(Set(chunk), { finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale=true, createLabel=false)
    newChunk
  }

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk = {
    decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.permPlus(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale)
  }

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk = {
    decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale)
  }

  def withPermNonQuantifiedChunk(chunk: NonQuantifiedChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): NonQuantifiedChunk = {
    decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale)
  }

  def permScale(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk = {
    decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      chunk.permScale(finalPerm, newPermExp)},
      newPerm, analysisInfos, isExhale)
  }

  def substitute(chunk: GeneralChunk, terms: silicon.Map[Term, Term], analysisInfos: DependencyAnalysisInfos, isExhale: Boolean=false): GeneralChunk = {
    val newChunk = chunk.substitute(terms)
    decider.registerDerivedChunk(Set(chunk), {finalPerm =>
      newChunk.withPerm(finalPerm, newChunk.permExp)},
      newChunk.perm, analysisInfos, isExhale)
  }

  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfos: DependencyAnalysisInfos): QuantifiedChunk = {
    decider.registerDerivedChunk[QuantifiedChunk](Set(chunk), {_ =>
      chunk.withSnapshotMap(snap)
    },
      chunk.perm, analysisInfos, isExhale=false, createLabel=false)
  }

  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfos: DependencyAnalysisInfos): NonQuantifiedChunk = {
    decider.registerDerivedChunk[NonQuantifiedChunk](Set(chunk), {_ =>
      chunk.withSnap(snap, snapExp)},
      chunk.perm, analysisInfos, isExhale=false, createLabel=false)
  }
}