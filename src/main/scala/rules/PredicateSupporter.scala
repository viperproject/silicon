// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.assumptionAnalysis.{AnalysisInfo, AssumptionType}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.VerificationResult
import viper.silicon.resources.PredicateID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission

trait PredicateSupportRules extends SymbolicExecutionRules {
  def fold(s: State,
           predicate: ast.Predicate,
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
           predicate: ast.Predicate,
           tArgs: List[Term],
           eArgs: Option[Seq[ast.Exp]],
           tPerm: Term,
           ePerm: Option[ast.Exp],
           constrainableWildcards: InsertionOrderedSet[Var],
           pve: PartialVerificationError,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
    val tArgsWithE = if (withExp)
      tArgs zip eArgs.get.map(Some(_))
    else
      tArgs zip Seq.fill(tArgs.length)(None)
    val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip tArgsWithE)
    val s1 = s.copy(g = gIns,
                    smDomainNeeded = true)
              .scalePermissionFactor(tPerm, ePerm)
    consume(s1, body, true, pve, v)((s1a, snap, consumedChunks, v1) => { // TODO ake: add edges from consumedChunks
      if (!Verifier.config.disableFunctionUnfoldTrigger()) {
        val predTrigger = App(s1a.predicateData(predicate).triggerFunction,
          snap.get.convert(terms.sorts.Snap) +: tArgs)
        val eArgsString = eArgs.mkString(", ")
        v1.decider.assume(predTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eArgsString))")), AssumptionType.Internal)
      }
      val s2 = s1a.setConstrainable(constrainableWildcards, false)
      if (s2.qpPredicates.contains(predicate)) {
        val predSnap = snap.get.convert(s2.predicateSnapMap(predicate))
        val formalArgs = s2.predicateFormalVarMap(predicate)
        val (sm, smValueDef) =
          quantifiedChunkSupporter.singletonSnapshotMap(s2, predicate, tArgs, predSnap, v1)
        v1.decider.prover.comment("Definitional axioms for singleton-SM's value")
        val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-SM's value", isInternal_ = true))
        v1.decider.assumeDefinition(smValueDef, debugExp, AssumptionType.Internal)
        val ch =
          quantifiedChunkSupporter.createSingletonQuantifiedChunk(
            formalArgs, Option.when(withExp)(predicate.formalArgs), predicate, tArgs, eArgs, tPerm, ePerm, sm, s.program, v1, AssumptionType.Rewrite)
        val h3 = s2.h + ch
        val smDef = SnapshotMapDefinition(predicate, sm, Seq(smValueDef), Seq())
        val smCache = if (s2.heapDependentTriggers.contains(predicate)) {
          val (relevantChunks, _) =
            quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h3, BasicChunkIdentifier(predicate.name))
          val (smDef1, smCache1) =
            quantifiedChunkSupporter.summarisingSnapshotMap(
              s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v1)
          val eArgsString = eArgs.mkString(", ")
          v1.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs),
            Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eArgsString))")), AssumptionType.Internal)
          smCache1
        } else {
          s2.smCache
        }

        val s3 = s2.copy(g = s.g,
                         h = h3,
                         smCache = smCache,
                         permissionScalingFactor = s.permissionScalingFactor,
                         permissionScalingFactorExp = s.permissionScalingFactorExp,
                         functionRecorder = s2.functionRecorder.recordFvfAndDomain(smDef))
        Q(s3, v1)
      } else {
        val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, eArgs, snap.get.convert(sorts.Snap), None, tPerm, ePerm, v1.decider.assumptionAnalyzer.getAnalysisInfo(AssumptionType.Rewrite))
        val s3 = s2.copy(g = s.g,
                         smDomainNeeded = s.smDomainNeeded,
                         permissionScalingFactor = s.permissionScalingFactor,
                         permissionScalingFactorExp = s.permissionScalingFactorExp)
        chunkSupporter.produce(s3, s3.h, ch, v1)((s4, h1, v2) =>
          Q(s4.copy(h = h1), v2))
      }
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
    if (s1.qpPredicates.contains(predicate)) {
      val formalVars = s1.predicateFormalVarMap(predicate)
      quantifiedChunkSupporter.consumeSingleLocation(
        s1,
        s1.h,
        formalVars,
        Option.when(withExp)(predicate.formalArgs),
        tArgs,
        eArgs,
        pa,
        tPerm,
        ePerm,
        true,
        None,
        pve,
        v
      )((s2, h2, snap, consumedChunks, v1) => {
        val s3 = s2.copy(g = gIns, h = h2)
                   .setConstrainable(constrainableWildcards, false)
        produce(s3, toSf(snap.get), body, pve, v1, AssumptionType.Rewrite)((s4, v2) => { // TODO ake: add edge from consumedChunks to new assumptions
          v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction,
                snap.get.convert(terms.sorts.Snap) +: tArgs)
            val eargs = eArgs.mkString(", ")
            v2.decider.assume(predicateTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eargs))")), AssumptionType.Internal)
          }
          Q(s4.copy(g = s.g,
                    permissionScalingFactor = s.permissionScalingFactor,
                    permissionScalingFactorExp = s.permissionScalingFactorExp),
            v2)})
      })
    } else {
      val ve = pve dueTo InsufficientPermission(pa)
      val description = s"consume ${pa.pos}: $pa"
      chunkSupporter.consume(s1, s1.h, predicate, tArgs, eArgs, s1.permissionScalingFactor, s1.permissionScalingFactorExp, true, ve, v, description)((s2, h1, snap, consumedChunks, v1) => { // TODO ake: add edges
        val s3 = s2.copy(g = gIns, h = h1)
                   .setConstrainable(constrainableWildcards, false)
        produce(s3, toSf(snap.get), body, pve, v1, AssumptionType.Rewrite)((s4, v2) => {
          v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterUnfold)
          if (!Verifier.config.disableFunctionUnfoldTrigger()) {
            val predicateTrigger =
              App(s4.predicateData(predicate).triggerFunction, snap.get +: tArgs)
            val eargs = eArgs.mkString(", ")
            v2.decider.assume(predicateTrigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${pa.predicateName}($eargs))")), AssumptionType.Internal)
          }
          val s5 = s4.copy(g = s.g,
                           permissionScalingFactor = s.permissionScalingFactor,
                           permissionScalingFactorExp = s.permissionScalingFactorExp)
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
