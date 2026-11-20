// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.state.chunks

import viper.silicon
import viper.silicon.decider.{Decider, DependencyAnalysisHandler}
import viper.silicon.dependencyAnalysis.{AnalysisInfos, AnalysisInfosForChunks}
import viper.silicon.resources.{BaseID, ResourceID}
import viper.silicon.rules.InverseFunctions
import viper.silicon.state.terms.{MagicWandSnapshot, Term, Var}
import viper.silver.ast
import viper.silver.dependencyAnalysis.OriginType

import scala.annotation.unused

class DependencyAnalysisAwareChunkFactory(decider: Decider with DependencyAnalysisHandler) extends ChunkFactory {
  override def createBasicChunk(resourceID: BaseID,
                                id: BasicChunkIdentifier,
                                args: Seq[Term],
                                argsExp: Option[Seq[ast.Exp]],
                                snap: Term,
                                snapExp: Option[ast.Exp],
                                perm: Term,
                                permExp: Option[ast.Exp],
                                tag: Option[Int],
                                analysisInfos: AnalysisInfosForChunks): BasicChunk = {
    decider.registerChunk[BasicChunk]({finalPerm =>
      BasicChunk(resourceID, id, args, argsExp, snap, snapExp, finalPerm, permExp, tag)
    },
      perm, analysisInfos)
  }

  override def createQuantifiedFieldChunk(id: BasicChunkIdentifier,
                                          fvf: Term,
                                          orgCondition: Term,
                                          condition: Term,
                                          conditionExp: Option[ast.Exp],
                                          permValue: Term,
                                          permValueExp: Option[ast.Exp],
                                          invs: Seq[InverseFunctions],
                                          singletonRcvr: Option[Term],
                                          singletonRcvrExp: Option[ast.Exp],
                                          tag: Option[Int],
                                          hints: Seq[Term] = Nil,
                                          analysisInfos: AnalysisInfosForChunks): QuantifiedFieldChunk = {
    decider.registerChunk[QuantifiedFieldChunk]({perm =>
      QuantifiedFieldChunk(id, fvf, orgCondition, condition, conditionExp, perm, permValueExp, invs, singletonRcvr, singletonRcvrExp, tag, hints)
    },
      permValue, analysisInfos)
  }

  override def createQuantifiedPredicateChunk(id: BasicChunkIdentifier,
                                              quantifiedVars: Seq[Var],
                                              quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                              psf: Term,
                                              orgCondition: Term,
                                              condition: Term,
                                              conditionExp: Option[ast.Exp],
                                              permValue: Term,
                                              permValueExp: Option[ast.Exp],
                                              invs: Seq[InverseFunctions],
                                              singletonArgs: Option[Seq[Term]],
                                              singletonArgExps: Option[Seq[ast.Exp]],
                                              tag: Option[Int],
                                              hints: Seq[Term] = Nil,
                                              analysisInfos: AnalysisInfosForChunks): QuantifiedPredicateChunk = {
    decider.registerChunk[QuantifiedPredicateChunk]({ finalPerm =>
      QuantifiedPredicateChunk(id, quantifiedVars, quantifiedVarExps, psf, orgCondition, condition, conditionExp, finalPerm, permValueExp, invs,
        singletonArgs, singletonArgExps, tag, hints)
    }, permValue, analysisInfos)
  }

  override def createQuantifiedMagicWandChunk(id: MagicWandIdentifier,
                                              quantifiedVars: Seq[Var],
                                              quantifiedVarExps: Option[Seq[ast.LocalVarDecl]],
                                              wsf: Term,
                                              orgCondition: Term,
                                              perm: Term,
                                              permExp: Option[ast.Exp],
                                              invs: Seq[InverseFunctions],
                                              singletonArgs: Option[Seq[Term]],
                                              singletonArgExps: Option[Seq[ast.Exp]],
                                              tag: Option[Int],
                                              hints: Seq[Term] = Nil,
                                              analysisInfos: AnalysisInfosForChunks): QuantifiedMagicWandChunk = {
    decider.registerChunk[QuantifiedMagicWandChunk]({ finalPerm =>
      QuantifiedMagicWandChunk(id, quantifiedVars, quantifiedVarExps, wsf, orgCondition, finalPerm, permExp, invs,
        singletonArgs, singletonArgExps, tag, hints)
    }, perm, analysisInfos)
  }

  override def createMagicWandChunk(id: MagicWandIdentifier,
                                    bindings: Map[ast.AbstractLocalVar, (Term, Option[ast.Exp])],
                                    args: Seq[Term],
                                    argsExp: Option[Seq[ast.Exp]],
                                    snap: MagicWandSnapshot,
                                    perm: Term,
                                    permExp: Option[ast.Exp],
                                    tag: Option[Int],
                                    analysisInfos: AnalysisInfosForChunks): MagicWandChunk = {
    decider.registerChunk[MagicWandChunk]({ finalPerm =>
      MagicWandChunk(id, bindings, args, argsExp, snap, finalPerm, permExp, tag)
    }, perm, analysisInfos)
  }

  def createBasicMaskHeapChunk(resourceID: ResourceID, resource: Any, mask: Term, heap: Term, analysisInfos: AnalysisInfosForChunks) : BasicMaskHeapChunk =
    BasicMaskHeapChunk(resourceID, resource, mask, heap)

  def applyCondition(chunk: GeneralChunk, newCond: Term, newCondExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): GeneralChunk = {
    decider.registerChunk({_ =>
      chunk.applyCondition(newCond, newCondExp)},
      chunk.perm, analysisInfos)
  }

  def permMinus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfos): GeneralChunk = {
    val newChunk = decider.registerChunk({finalPerm =>
      chunk.permMinus(finalPerm, newPermExp)},
      newPerm, analysisInfos.overrideDependencyType(OriginType.Internal).forChunk)
    @unused // we need to register the chunk to have a sound analysis
    val exhaledChunk = decider.registerChunk({ finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos.forExhaledChunk)
    newChunk
  }

  def permMinus(chunk: QuantifiedBasicChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfos): QuantifiedBasicChunk = {
    val newChunk = decider.registerChunk({finalPerm =>
      chunk.permMinus(finalPerm, newPermExp)},
      newPerm, analysisInfos.overrideDependencyType(OriginType.Internal).forChunk)
    @unused // we need to register the chunk to have a sound analysis
    val exhaledChunk = decider.registerChunk({ finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos.forExhaledChunk)
    newChunk
  }

  def permPlus(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): GeneralChunk = {
    decider.registerChunk({finalPerm =>
      chunk.permPlus(finalPerm, newPermExp)},
      newPerm, analysisInfos)
  }

  def withPerm(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): GeneralChunk = {
    decider.registerChunk({finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos)
  }

  def withPermNonQuantifiedChunk(chunk: NonQuantifiedChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): NonQuantifiedChunk = {
    decider.registerChunk({finalPerm =>
      chunk.withPerm(finalPerm, newPermExp)},
      newPerm, analysisInfos)
  }

  def permScale(chunk: GeneralChunk, newPerm: Term, newPermExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): GeneralChunk = {
    decider.registerChunk({finalPerm =>
      chunk.permScale(finalPerm, newPermExp)},
      newPerm, analysisInfos)
  }

  def substitute(chunk: GeneralChunk, terms: silicon.Map[Term, Term], analysisInfos: AnalysisInfosForChunks): GeneralChunk = {
    val newChunk = chunk.substitute(terms)
    decider.registerChunk({ finalPerm =>
      newChunk.withPerm(finalPerm, newChunk.permExp)
    },
      newChunk.perm, analysisInfos)
  }

  def substitute(chunk: Chunk, terms: silicon.Map[Term, Term], analysisInfos: AnalysisInfosForChunks): Chunk = {
    chunk match {
      case ch: GeneralChunk => substitute(ch, terms, analysisInfos)
      case ch: MaskHeapChunk => ch.substitute(terms)
    }
  }

  def withSnapshotMap(chunk: QuantifiedChunk, snap: Term, analysisInfos: AnalysisInfosForChunks): QuantifiedChunk = {
    decider.registerChunk[QuantifiedChunk]({_ =>
      chunk.withSnapshotMap(snap)
    },
      chunk.perm, analysisInfos)
  }

  def withSnap(chunk: NonQuantifiedChunk, snap: Term, snapExp: Option[ast.Exp], analysisInfos: AnalysisInfosForChunks): NonQuantifiedChunk = {
    decider.registerChunk[NonQuantifiedChunk]({_ =>
      chunk.withSnap(snap, snapExp)},
      chunk.perm, analysisInfos)
  }
}