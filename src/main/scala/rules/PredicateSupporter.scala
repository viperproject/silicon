// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.VerificationResult
import viper.silicon.resources.PredicateID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier

trait PredicateSupportRules extends SymbolicExecutionRules {
  def fold(s: State,
           predicate: ast.Predicate,
           tArgs: List[Term],
           tPerm: Term,
           constrainableWildcards: InsertionOrderedSet[Var],
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             tPerm: Term,
             constrainableWildcards: InsertionOrderedSet[Var],
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess /* TODO: Make optional */)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object predicateSupporter extends PredicateSupportRules {
  import consumer._
  import producer._

  def fold(s: State,
           predicate: ast.Predicate,
           tArgs: List[Term],
           tPerm: Term,
           constrainableWildcards: InsertionOrderedSet[Var],
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
    val s1 = s.copy(g = gIns,
                    smDomainNeeded = true)
              .scalePermissionFactor(tPerm)
    consume(s1, body, pve, v)((s1a, snap, v1) => {
      if (!Verifier.config.disableFunctionUnfoldTrigger()) {
        val predTrigger = App(s1a.predicateData(predicate).triggerFunction,
          snap.convert(terms.sorts.Snap) +: tArgs)
        v1.decider.assume(predTrigger)
      }
      val s2 = s1a.setConstrainable(constrainableWildcards, false)
      if (s2.qpPredicates.contains(predicate)) {
        val predSnap = snap.convert(s2.predicateSnapMap(predicate))
        val formalArgs = s2.predicateFormalVarMap(predicate)
        val (sm, smValueDef) =
          quantifiedChunkSupporter.singletonSnapshotMap(s2, predicate, tArgs, predSnap, v1)
        v1.decider.prover.comment("Definitional axioms for singleton-SM's value")
        v1.decider.assume(smValueDef)
        val ch =
          quantifiedChunkSupporter.createSingletonQuantifiedChunk(
            formalArgs, predicate, tArgs, tPerm, sm, s.program)
        val h3 = s2.h + ch
        val smDef = SnapshotMapDefinition(predicate, sm, Seq(smValueDef), Seq())
        val smCache = if (s2.heapDependentTriggers.contains(predicate)) {
          val (relevantChunks, _) =
            quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h3, BasicChunkIdentifier(predicate.name))
          val (smDef1, smCache1) =
            quantifiedChunkSupporter.summarisingSnapshotMap(
              s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v1)
          v1.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs))
          smCache1
        } else {
          s2.smCache
        }

        val s3 = s2.copy(g = s.g,
                         h = h3,
                         smCache = smCache,
                         functionRecorder = s2.functionRecorder.recordFvfAndDomain(smDef))
        Q(s3, v1)
      } else {
        val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, snap.convert(sorts.Snap), tPerm)
        val s3 = s2.copy(g = s.g,
                         smDomainNeeded = s.smDomainNeeded,
                         permissionScalingFactor = s.permissionScalingFactor)
        chunkSupporter.produce(s3, s3.h, ch, v1)((s4, h1, v2) =>
          Q(s4.copy(h = h1), v2))
      }
    })
  }

  def unfold(s: State,
             predicate: ast.Predicate,
             tArgs: List[Term],
             tPerm: Term,
             constrainableWildcards: InsertionOrderedSet[Var],
             pve: PartialVerificationError,
             v: Verifier,
             pa: ast.PredicateAccess)
            (Q: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val s1 = s.scalePermissionFactor(tPerm)
    if (s1.qpPredicates.contains(predicate)) {
      val formalVars = s1.predicateFormalVarMap(predicate)
      quantifiedChunkSupporter.consumeSingleLocation(
        s1,
        s1.h,
        formalVars,
        tArgs,
        pa,
        tPerm,
        None,
        pve,
        v
      )((s2, h2, snap, v1) => {
        val s3 = s2.copy(g = gIns, h = h2)
                   .setConstrainable(constrainableWildcards, false)
        produce(s3, toSf(snap), body, pve, v1)((s4, v2) => {
          v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction,
                snap.convert(terms.sorts.Snap) +: tArgs)
            v2.decider.assume(predicateTrigger)
          }
          Q(s4.copy(g = s.g,
                    permissionScalingFactor = s.permissionScalingFactor),
            v2)})
      })
    } else {
      val ve = pve dueTo InsufficientPermission(pa)
      val description = s"consume ${pa.pos}: $pa"
      chunkSupporter.consume(s1, s1.h, predicate, tArgs, s1.permissionScalingFactor, ve, v, description)((s2, h1, snap, v1) => {
        val s3 = s2.copy(g = gIns, h = h1)
                   .setConstrainable(constrainableWildcards, false)
        produce(s3, toSf(snap), body, pve, v1)((s4, v2) => {
          v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction, snap +: tArgs)
            v2.decider.assume(predicateTrigger)
          }
          val s5 = s4.copy(g = s.g,
                           permissionScalingFactor = s.permissionScalingFactor)
          Q(s5, v2)})})
    }
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
