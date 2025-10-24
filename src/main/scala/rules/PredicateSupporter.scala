// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon
import viper.silicon.Config.JoinMode
import viper.silicon.debugger.DebugExp
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.{ChunkIdentifer, GeneralChunk, MaskHeapChunk, NonQuantifiedChunk}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.sorts.PredHeapSort
import viper.silicon.resources.FieldID
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.{PredicateBranchNode, PredicateLeafNode, PredicateContentsTree}
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError

import scala.collection.immutable

trait PredicateSupportRules extends SymbolicExecutionRules {
  def fold(s: State,
           pa: ast.PredicateAccess,
           tArgs: List[Term],
           eArgs: Option[Seq[ast.Exp]],
           tPerm: Term,
           ePerm: Option[ast.Exp],
           constrainableWildcards: InsertionOrderedSet[Var],
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             eArgs: Option[Seq[ast.Exp]],
             tPerm: Term,
             ePerm: Option[ast.Exp],
             constrainableWildcards: InsertionOrderedSet[Var],
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object predicateSupporter extends PredicateSupportRules {
  import consumer._
  import producer._

  def fold(s: State,
           pa: ast.PredicateAccess,
           tArgs: List[Term],
           eArgs: Option[Seq[ast.Exp]],
           tPerm: Term,
           ePerm: Option[ast.Exp],
           constrainableWildcards: InsertionOrderedSet[Var],
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    val predicate = pa.loc(s.program)
    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val tArgsWithE = if (withExp)
      tArgs zip eArgs.get.map(Some(_))
    else
      tArgs zip Seq.fill(tArgs.length)(None)
    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgsWithE)
    val s1 = s.copy(g = gIns,
                    smDomainNeeded = true)
              .scalePermissionFactor(tPerm, ePerm)
    consume(s1, body, true, pve, v)((s1a, snap, v1) => {
      if (!Verifier.config.disableFunctionUnfoldTrigger()) {
        val snapArg = if (Verifier.config.maskHeapMode()) {
          val chunk = s1a.h.values.find(c => c.asInstanceOf[MaskHeapChunk].resource == predicate).get.asInstanceOf[BasicMaskHeapChunk]
          chunk.heap
        } else {
          snap.get.convert(sorts.Snap)
        }
        val predTrigger = App(s1a.predicateData(predicate).triggerFunction,
          snapArg +: tArgs)
        val eArgsString = eArgs.mkString(", ")
        v1.decider.assume(predTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eArgsString))")))
      }
      val s2 = s1a.copy(g = s.g,
                        smDomainNeeded = s.smDomainNeeded,
                        permissionScalingFactor = s.permissionScalingFactor,
                        permissionScalingFactorExp = s.permissionScalingFactorExp).setConstrainable(constrainableWildcards, false)

      val snapToProduce = if (Verifier.config.maskHeapMode()) {
        val tmp = v1.decider.createAlias(HeapToSnap(HeapSingleton(toSnapTree(tArgs), snap.get, PredHeapSort),
          HeapUpdate(PredZeroMask, toSnapTree(tArgs), FullPerm), predicate), s2)
        FakeMaskMapTerm(immutable.ListMap(predicate -> SnapToHeap(tmp, predicate, PredHeapSort)))
      } else {
        snap.get.convert(s2.predicateSnapMap(predicate))
      }
      v1.heapSupporter.produceSingle(s2, predicate, tArgs, eArgs, snapToProduce, None, tPerm, ePerm, pve, true, v1)((s3, v3) => {
        val s4 = v3.heapSupporter.triggerResourceIfNeeded(s3, pa, tArgs, eArgs, v3)
        Q(s4, v3)
      })
    })
  }

  def producePredicateContents(s: State, tree: PredicateContentsTree, toReplace: silicon.Map[Term, Term], v: Verifier, isUnfolding: Boolean = false)
                              (Q: (State, Verifier) => VerificationResult)
            : VerificationResult = {
    tree match {
      case PredicateLeafNode(h, assumptions) =>
        val debugExp = Option.when(withExp)(DebugExp.createInstance("Assumption from unfolded predicate body"))
        v.decider.assume(assumptions.map(a => (a.replace(toReplace), debugExp)).toSeq)
        val substChunks = h.values.map(_.substitute(toReplace).asInstanceOf[GeneralChunk].permScale(s.permissionScalingFactor, s.permissionScalingFactorExp))

        val quantifiedResourceIdentifiers: Set[ChunkIdentifer] = s.qpPredicates.map(p => BasicChunkIdentifier(p.name)) ++ s.qpFields.map(f => BasicChunkIdentifier(f.name)) ++ s.qpMagicWands

        var newFr = s.functionRecorder
        val substChunksOptQps = substChunks.map(c => {
          if (quantifiedResourceIdentifiers.contains(c.id) && c.isInstanceOf[NonQuantifiedChunk]) {
            c match {
              case bc: BasicChunk =>
                val resource = bc.resourceID match {
                  case FieldID => s.program.findField(bc.id.name)
                  case _ => s.program.findPredicate(bc.id.name)
                }
                val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, resource, bc.args, bc.snap, v)
                v.decider.assumeDefinition(smValueDef, None)
                val codQvars = bc.resourceID match {
                  case FieldID => Seq(`?r`)
                  case _ => s.predicateFormalVarMap(resource.asInstanceOf[ast.Predicate])
                }
                newFr = newFr.recordFvfAndDomain(SnapshotMapDefinition(resource, sm, Seq(smValueDef), Seq()))
                quantifiedChunkSupporter.createSingletonQuantifiedChunk(codQvars, None, resource, bc.args, None, bc.perm, None, sm, s.program)
              case mwc: MagicWandChunk =>
                val wand = mwc.id.ghostFreeWand
                val bodyVars = wand.subexpressionsToEvaluate(s.program)
                val codQvars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
                val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, wand, mwc.args, mwc.snap, v)
                v.decider.assumeDefinition(smValueDef, None)
                newFr = newFr.recordFvfAndDomain(SnapshotMapDefinition(wand, sm, Seq(smValueDef), Seq()))
                quantifiedChunkSupporter.createSingletonQuantifiedChunk(codQvars, None, wand, mwc.args, None, mwc.perm, None, sm, s.program)
            }
          } else {
            c
          }
        })
        val substHeap = Heap(substChunksOptQps)
        val (fr1, h1) = v.stateConsolidator(s).merge(newFr, s, s.h, substHeap, v)
        val s1 = s.copy(h = h1, functionRecorder = fr1)

        Q(s1, v)
      case PredicateBranchNode(cond, condExp, left, right) =>
        val substCond = cond.replace(toReplace)

        if (!isUnfolding && s.moreJoins.id >= JoinMode.Impure.id) {
          joiner.join[scala.Null, scala.Null](s, v, resetState = false)((s1, v1, QB) => {
            brancher.branch(s1, substCond, condExp, v1)(
              (s2, v2) => {
                producePredicateContents(s2, left, toReplace, v2, isUnfolding)((s3, v3) => QB(s3, null, v3))
              },
              (s2, v2) => {
                producePredicateContents(s2, right, toReplace, v2, isUnfolding)((s3, v3) => QB(s3, null, v3))
              }
            )
          }) (entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMergeWithoutConsolidation(entry2, v)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")
            }
            (s2, null)
          }) ((sp, _, vp) => Q(sp, vp))
        } else {
          brancher.branch(s, substCond, condExp, v)(
            (s1, v1) => {
              producePredicateContents(s1, left, toReplace, v1, isUnfolding)(Q)
            },
            (s2, v2) => {
              producePredicateContents(s2, right, toReplace, v2, isUnfolding)(Q)
            }
          )
        }
    }
  }

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             eArgs: Option[Seq[ast.Exp]],
             tPerm: Term,
             ePerm: Option[ast.Exp],
             constrainableWildcards: InsertionOrderedSet[Var],
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val tArgsWithE = if (withExp)
      tArgs zip eArgs.get.map(Some(_))
    else
      tArgs zip Seq.fill(tArgs.length)(None)
    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgsWithE)
    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val s1 = s.scalePermissionFactor(tPerm, ePerm)

    v.heapSupporter.consumeSingle(s1, s1.h, pa, tArgs, eArgs, tPerm, ePerm, true, pve, v)((s2, h2, snap, v1) => {
      val s3 = s2.copy(g = gIns, h = h2)
        .setConstrainable(constrainableWildcards, false)

      if (s3.predicateData(predicate).predContents.isDefined) {
        val toReplace: silicon.Map[Term, Term] = silicon.Map.from(s3.predicateData(predicate).params.get.zip(Seq(snap.get) ++ tArgs))
        producePredicateContents(s3, s3.predicateData(predicate).predContents.get, toReplace, v1, false)((s4, v4) => {
          v4.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction,
                snap.get.convert(terms.sorts.Snap) +: tArgs)
            val eargs = eArgs.mkString(", ")
            v4.decider.assume(predicateTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eargs))")))
          }
          Q(s4.copy(g = s.g,
            permissionScalingFactor = s.permissionScalingFactor,
            permissionScalingFactorExp = s.permissionScalingFactorExp),
            v4)
        })
      } else {
        val newSf = if (Verifier.config.maskHeapMode()) {
          val packedSnap = maskHeapSupporter.convertToSnapshot(snap.get.asInstanceOf[FakeMaskMapTerm].masks, Seq(predicate), magicWandSupporter.getEvalHeap(s, v1), s2, v1.decider)

          val predSnap = packedSnap match {
            case FakeMaskMapTerm(masks) => HeapLookup(masks(predicate), toSnapTree(tArgs))
            case h2s: HeapToSnap => HeapLookup(h2s.heap, toSnapTree(tArgs))
            case _ => HeapLookup(v1.decider.createAlias(SnapToHeap(snap.get, predicate, PredHeapSort), s3), toSnapTree(tArgs))
          }
          (_: Sort, _: Verifier) => predSnap
        } else {
          toSf(snap.get)
        }
        produce(s3, newSf, body, pve, v1)((s4, v2) => {
          v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction,
                snap.get.convert(terms.sorts.Snap) +: tArgs)
            val eargs = eArgs.mkString(", ")
            v2.decider.assume(predicateTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eargs))")))
          }
          Q(s4.copy(g = s.g,
            permissionScalingFactor = s.permissionScalingFactor,
            permissionScalingFactorExp = s.permissionScalingFactorExp),
            v2)
        })
      }
    })
  }
}
