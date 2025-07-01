// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.MaskHeapChunk
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.sorts.PredHeapSort
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
        val tmp = HeapToSnap(HeapSingleton(toSnapTree(tArgs), snap.get, PredHeapSort),
          HeapUpdate(PredZeroMask, toSnapTree(tArgs), FullPerm), predicate)
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

      val newSf = if (Verifier.config.maskHeapMode()) {
        val packedSnap = maskHeapSupporter.convertToSnapshot(snap.get.asInstanceOf[FakeMaskMapTerm].masks, Seq(predicate), s.h, s2, v1.decider)

        val predSnap = packedSnap match {
          case FakeMaskMapTerm(masks) => HeapLookup(masks(predicate), toSnapTree(tArgs))
          case h2s: HeapToSnap => HeapLookup(h2s.heap, toSnapTree(tArgs))
          case _ => HeapLookup(SnapToHeap(snap.get, predicate, PredHeapSort), toSnapTree(tArgs))
        }
        (_: Sort, _: Verifier) => predSnap
      } else {
        toSf(snap.get)
      }

      produce(s3, newSf, body, pve, v1)((s4, v2) => {
        v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
        if (!Verifier.config.disableFunctionUnfoldTrigger()) {
          val snapArg = if (Verifier.config.maskHeapMode()) {
            val chunk = s4.h.values.find(c => c.asInstanceOf[MaskHeapChunk].resource == predicate).get.asInstanceOf[BasicMaskHeapChunk]
            chunk.heap
          } else {
            snap.get.convert(sorts.Snap)
          }
          val predicateTrigger =
            App(s4.predicateData(predicate).triggerFunction,
              snapArg +: tArgs)
          val eargs = eArgs.mkString(", ")
          v2.decider.assume(predicateTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eargs))")))
        }
        Q(s4.copy(g = s.g,
          permissionScalingFactor = s.permissionScalingFactor,
          permissionScalingFactorExp = s.permissionScalingFactorExp),
          v2)
      })
    })
  }

/* NOTE: Possible alternative to storing the permission scaling factor in the context
 *       or passing it to produce/consume as an explicit argument.
 *       Carbon uses Permissions.multiplyExpByPerm as well (but does not extend the
 *       store).
 */
//    private def scale(γ: ST, body: ast.Exp, perm: Term) = {
//      /* TODO: Ensure that variable name does not clash with any Silver identifier already in use */
//      val scaleFactorVar = ast.LocalVar(identifierFactory.fresh("p'unf").name)(ast.Perm)
//      val scaledBody = ast.utility.Permissions.multiplyExpByPerm(body, scaleFactorVar)
//
//      (γ + (scaleFactorVar -> perm), scaledBody)
//    }
}
