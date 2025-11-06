// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.VerificationResult
import viper.silicon.interfaces.state.{ChunkIdentifer, NonQuantifiedChunk}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.rules.havocSupporter.{HavocHelperData, HavocOneData, HavocallData}
import viper.silicon.rules.quantifiedChunkSupporter.freshSnapshotMap
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, ChunkIdentifier, Heap, MagicWandChunk, MagicWandIdentifier, QuantifiedBasicChunk, QuantifiedFieldChunk, QuantifiedMagicWandChunk, QuantifiedPredicateChunk, State, Store}
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.{`?r`, `?s`}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.ast.{BigAnd, replaceVarsInExp}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.parser.PUnknown
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{ErrorReason, PartialVerificationError, VerificationError}


trait HeapSupportRules extends SymbolicExecutionRules {

  def evalFieldAccess(s: State,
                      fa: ast.FieldAccess,
                      tRcvr: Term,
                      eRcvr: Option[ast.Exp],
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult)
                     : VerificationResult

  def evalCurrentPerm(s: State,
                      h: Heap,
                      resAcc: ast.ResourceAccess,
                      identifier: ChunkIdentifer,
                      tArgs: Seq[Term],
                      eArgs: Option[Seq[ast.Exp]],
                      v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult): VerificationResult

  def isPossibleTrigger(s: State, fa: ast.FieldAccess): Boolean

  def execFieldAssign(s: State,
                      ass: ast.FieldAssign,
                      tRcvr: Term,
                      eRcvrNew: Option[ast.Exp],
                      tRhs: Term,
                      eRhsNew: Option[ast.Exp],
                      pve: PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
                     : VerificationResult

  def triggerResourceIfNeeded(s: State,
                              resAcc: ast.ResourceAccess,
                              tArgs: Seq[Term],
                              eArgs: Option[Seq[ast.Exp]],
                              v: Verifier): State

  def consumeSingle(s: State,
                    h: Heap,
                    resAcc: ast.ResourceAccess,
                    tArgs: Seq[Term],
                    eArgs: Option[Seq[ast.Exp]],
                    tPerm: Term,
                    ePerm: Option[ast.Exp],
                    returnSnap: Boolean,
                    pve: PartialVerificationError,
                    v: Verifier)
                   (Q: (State, Heap, Option[Term], Verifier) => VerificationResult): VerificationResult

  def consumeQuantified(s: State,
                        h: Heap,
                        resource: ast.Resource,
                        qvars: Seq[Var],
                        qvarExps: Option[Seq[ast.LocalVarDecl]],
                        tFormalArgs: Seq[Var],
                        eFormalArgs: Option[Seq[ast.LocalVarDecl]],
                        qid: String,
                        optTrigger: Option[Seq[ast.Trigger]],
                        tTriggers: Seq[Trigger],
                        auxGlobals: Seq[Term],
                        auxNonGlobals: Seq[Quantification],
                        auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        tCond: Term,
                        eCond: Option[ast.Exp],
                        tArgs: Seq[Term],
                        eArgs: Option[Seq[ast.Exp]],
                        tPerm: Term,
                        ePerm: Option[ast.Exp],
                        returnSnap: Boolean,
                        pve: PartialVerificationError,
                        negativePermissionReason: => ErrorReason,
                        notInjectiveReason: => ErrorReason,
                        insufficientPermissionReason: => ErrorReason,
                        v: Verifier)
                       (Q: (State, Heap, Option[Term], Verifier) => VerificationResult): VerificationResult

  def produceSingle(s: State,
                    resource: ast.Resource,
                    tArgs: Seq[Term],
                    eArgs: Option[Seq[ast.Exp]],
                    tSnap: Term,
                    eSnap: Option[ast.Exp],
                    tPerm: Term,
                    ePerm: Option[ast.Exp],
                    pve: PartialVerificationError,
                    mergeAndTrigger: Boolean,
                    v: Verifier)
                   (Q: (State, Verifier) => VerificationResult): VerificationResult

  def produceQuantified(s: State,
                        sf: (Sort, Verifier) => Term,
                        forall: ast.Forall,
                        resource: ast.Resource,
                        qvars: Seq[Var],
                        qvarExps: Option[Seq[ast.LocalVarDecl]],
                        tFormalArgs: Seq[Var],
                        eFormalArgs: Option[Seq[ast.LocalVarDecl]],
                        qid: String,
                        optTrigger: Option[Seq[ast.Trigger]],
                        tTriggers: Seq[Trigger],
                        auxGlobals: Seq[Term],
                        auxNonGlobals: Seq[Quantification],
                        auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        tCond: Term,
                        eCond: Option[ast.Exp],
                        tArgs: Seq[Term],
                        eArgs: Option[Seq[ast.Exp]],
                        tPerm: Term,
                        ePerm: Option[ast.Exp],
                        pve: PartialVerificationError,
                        negativePermissionReason: => ErrorReason,
                        notInjectiveReason: => ErrorReason,
                        v: Verifier)
                       (Q: (State, Verifier) => VerificationResult): VerificationResult

  def havocResource(s: State,
                    lhs: Term,
                    resource: ast.Resource,
                    condInfo: HavocHelperData,
                    v: Verifier): Heap

  def collectForPermConditions(s: State,
                               resource: ast.Resource,
                               qVars: Seq[(Var, ast.LocalVar)],
                               tArgs: Seq[Term],
                               eArgs: Option[Seq[ast.Exp]]): Seq[(Term, (ast.Exp, Option[ast.Exp]), Seq[Var], Store, Seq[Trigger])]

  def getEmptyHeap(program: ast.Program): Heap

}

class DefaultHeapSupportRules extends HeapSupportRules {
  def isPossibleTrigger(s: State, fa: ast.FieldAccess): Boolean = {
    s.qpFields.contains(fa.field)
  }

  def execFieldAssign(s: State,
                      ass: ast.FieldAssign,
                      tRcvr: Term,
                      eRcvrNew: Option[ast.Exp],
                      tRhs: Term,
                      eRhsNew: Option[ast.Exp],
                      pve: PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {
    val field = ass.lhs.field
    val ve = pve dueTo InsufficientPermission(ass.lhs)
    if (s.qpFields.contains(field)) {
      val (relevantChunks, otherChunks) =
        quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s.h, BasicChunkIdentifier(field.name))
      val hints = quantifiedChunkSupporter.extractHints(None, Seq(tRcvr))
      val chunkOrderHeuristics = quantifiedChunkSupporter.singleReceiverChunkOrderHeuristic(Seq(tRcvr), hints, v)
      val s2 = triggerResourceIfNeeded(s, ass.lhs, Seq(tRcvr), eRcvrNew.map(Seq(_)), v)
      v.decider.clearModel()
      val result = quantifiedChunkSupporter.removePermissions(
        s2,
        relevantChunks,
        Seq(`?r`),
        Option.when(withExp)(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())),
        `?r` === tRcvr,
        eRcvrNew.map(r => ast.EqCmp(ast.LocalVar(`?r`.id.name, ast.Ref)(), r)()),
        Some(Seq(tRcvr)),
        field,
        FullPerm,
        Option.when(withExp)(ast.FullPerm()()),
        chunkOrderHeuristics,
        v
      )
      result match {
        case (Complete(), s3, remainingChunks) =>
          val h3 = Heap(remainingChunks ++ otherChunks)
          val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s3, field, Seq(tRcvr), tRhs, v)
          v.decider.prover.comment("Definitional axioms for singleton-FVF's value")
          val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-FVF's value", isInternal_ = true))
          v.decider.assumeDefinition(smValueDef, debugExp)
          val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)(ass.pos, ass.info, ass.errT))),
            field, Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)), sm, s.program)
          if (s3.heapDependentTriggers.contains(field)) {
            val debugExp2 = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvrNew.toString()}.${field.name})"))
            v.decider.assume(FieldTrigger(field.name, sm, tRcvr), debugExp2)
          }
          val s4 = s3.copy(h = h3 + ch)
          val (debugHeapName, _) = v.getDebugOldLabel(s4, ass.lhs.pos)
          val s5 = if (withExp) s4.copy(oldHeaps = s4.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s4))) else s4
          Q(s5, v)
        case (Incomplete(_, _), s3, _) =>
          createFailure(ve, v, s3, "sufficient permission")
      }
    } else {
      val description = s"consume ${ass.pos}: $ass"
      chunkSupporter.consume(s, s.h, field, Seq(tRcvr), eRcvrNew.map(Seq(_)), FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)), false, ve, v, description)((s3, h3, _, v3) => {
        val id = BasicChunkIdentifier(field.name)
        val newChunk = BasicChunk(FieldID, id, Seq(tRcvr), eRcvrNew.map(Seq(_)), tRhs, eRhsNew, FullPerm, Option.when(withExp)(ast.FullPerm()(ass.pos, ass.info, ass.errT)))
        chunkSupporter.produce(s3, h3, newChunk, v3)((s4, h4, v4) => {
          val s5 = s4.copy(h = h4)
          val (debugHeapName, _) = v4.getDebugOldLabel(s5, ass.lhs.pos)
          val s6 = if (withExp) s5.copy(oldHeaps = s5.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s5))) else s5
          Q(s6, v4)
        })
      })
    }
  }

  def evalCurrentPerm(s: State,
                      h: Heap,
                      resAcc: ast.ResourceAccess,
                      identifier: ChunkIdentifer,
                      tArgs: Seq[Term],
                      eArgs: Option[Seq[ast.Exp]],
                      v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult): VerificationResult =
    {
      val res = resAcc.res(s.program)
      /* It is assumed that, for a given field/predicate/wand identifier (res)
       * either only quantified or only non-quantified chunks are used.
       */
      val usesQPChunks = s.isQuantifiedResource(res)
      val (s2, currentPermAmount) =
        if (usesQPChunks) {
          val formalVars = s.getFormalArgVars(res, v)

          val (relevantChunks, _) =
            quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](h, identifier)

          val (s2, smDef, pmDef) =
            quantifiedChunkSupporter.heapSummarisingMaps(
              s, res, formalVars, relevantChunks, v)
          if (s2.isUsedAsTrigger(res)) {
            val trigger = ResourceTriggerFunction(res, smDef.sm, tArgs, s.program)
            val argsString = eArgs.mkString(", ")
            v.decider.assume(trigger, Option.when(withExp)({
              val name = res match {
                case f: ast.Field => f.name
                case p: ast.Predicate => p.name
                case w: ast.MagicWand => MagicWandIdentifier(w, s2.program).toString
              }
              DebugExp.createInstance(s"Resource trigger(${name}($argsString))", isInternal_ = true)
            }))
          }

          val currentPermAmount = ResourcePermissionLookup(res, pmDef.pm, tArgs, s2.program)

          val s3 = res match {
            case _: ast.Field =>
              v.decider.prover.comment(s"perm($resAcc)  ~~>  assume upper permission bound")
              val (debugHeapName, debugLabel) = v.getDebugOldLabel(s2, resAcc.pos, Some(h))
              val exp = Option.when(withExp)(ast.PermLeCmp(ast.DebugLabelledOld(ast.CurrentPerm(resAcc)(), debugLabel)(), ast.FullPerm()())())
              v.decider.assume(PermAtMost(currentPermAmount, FullPerm), exp, exp.map(s2.substituteVarsInExp(_)))
              val s3 = if (Verifier.config.enableDebugging()) s2.copy(oldHeaps = s2.oldHeaps + (debugHeapName -> h)) else s2
              s3
            case _ => s2
          }

          (s3, currentPermAmount)
        } else {
          val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
          val currentPermAmount =
            chs.foldLeft(NoPerm: Term)((q, ch) => {
              val argsPairWiseEqual = And(tArgs.zip(ch.args).map { case (a1, a2) => a1 === a2 })
              PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm))
            })
          (s, currentPermAmount)
        }
      Q(s2, currentPermAmount, v)
    }

  def evalFieldAccess(s: State,
                      fa: ast.FieldAccess,
                      tRcvr: Term,
                      eRcvr: Option[ast.Exp],
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    if (s.qpFields.contains(fa.field)) {
      val (relevantChunks, _) =
        quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s.h, BasicChunkIdentifier(fa.field.name))
      s.smCache.get((fa.field, relevantChunks)) match {
        case Some((fvfDef: SnapshotMapDefinition, totalPermissions)) if !Verifier.config.disableValueMapCaching() =>
          /* The next assertion must be made if the FVF definition is taken from the cache;
           * in the other case it is part of quantifiedChunkSupporter.withValue.
           */
          /* Re-emit definition since the previous definition could be nested under
           * an auxiliary quantifier (resulting from the evaluation of some Silver
           * quantifier in whose body field 'fa.field' was accessed)
           * which is protected by a trigger term that we currently don't have.
           */
          v.decider.assume(And(fvfDef.valueDefinitions), Option.when(withExp)(DebugExp.createInstance("Value definitions", isInternal_ = true)))
          if (s.heapDependentTriggers.contains(fa.field)) {
            val trigger = FieldTrigger(fa.field.name, fvfDef.sm, tRcvr)
            val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
            v.decider.assume(trigger, triggerExp)
          }
          if (s.triggerExp) {
            val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
            val fr1 = s.functionRecorder.recordSnapshot(fa, v.decider.pcs.branchConditions, fvfLookup)
            val s2 = s.copy(functionRecorder = fr1)
            Q(s2, fvfLookup, v)
          } else {
            val toAssert = IsPositive(totalPermissions.replace(`?r`, tRcvr))
            v.decider.assert(toAssert) {
              case false =>
                createFailure(ve, v, s, toAssert, Option.when(withExp)(perms.IsPositive(ast.CurrentPerm(fa)())()))
              case true =>
                val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                val fr1 = s.functionRecorder.recordSnapshot(fa, v.decider.pcs.branchConditions, fvfLookup).recordFvfAndDomain(fvfDef)
                val possTriggers = if (s.heapDependentTriggers.contains(fa.field) && s.recordPossibleTriggers)
                  s.possibleTriggers + (fa -> FieldTrigger(fa.field.name, fvfDef.sm, tRcvr))
                else
                  s.possibleTriggers
                val s2 = s.copy(functionRecorder = fr1, possibleTriggers = possTriggers)
                Q(s2, fvfLookup, v)
            }
          }
        case _ =>
          val (s2, totalPerms, sm) = if (relevantChunks.size == 1) {
            val permVal = relevantChunks.head.perm
            val totalPermissions = permVal.replace(relevantChunks.head.quantifiedVars, Seq(tRcvr))
            (s, totalPermissions, relevantChunks.head.fvf)
          } else {
            val (s2, smDef1, pmDef1) =
              quantifiedChunkSupporter.heapSummarisingMaps(
                s = s,
                resource = fa.field,
                codomainQVars = Seq(`?r`),
                relevantChunks = relevantChunks,
                optSmDomainDefinitionCondition = None,
                optQVarsInstantiations = None,
                v = v)
            val perms = PermLookup(fa.field.name, pmDef1.pm, tRcvr)
            (s2.copy(functionRecorder = s.functionRecorder.recordFvfAndDomain(smDef1).recordPermMap(pmDef1)), perms, smDef1.sm)
          }
          if (s2.heapDependentTriggers.contains(fa.field)) {
            val trigger = FieldTrigger(fa.field.name, sm, tRcvr)
            val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
            v.decider.assume(trigger, triggerExp)
          }
          val (permCheck, permCheckExp, s3) =
            if (s2.triggerExp) {
              (True, Option.when(withExp)(ast.TrueLit()()), s2)
            } else {
              val (s3, lhs) = tRcvr match {
                case _: Literal | _: Var => (s2, True)
                case _ =>
                  // Make sure the receiver exists on the SMT level and is thus able to trigger any relevant quantifiers.
                  val rcvrVar = v.decider.appliedFresh("rcvr", tRcvr.sort, s2.relevantQuantifiedVariables.map(_._1))
                  val newFuncRec = s2.functionRecorder.recordFreshSnapshot(rcvrVar.applicable.asInstanceOf[Function])
                  (s2.copy(functionRecorder = newFuncRec), BuiltinEquals(rcvrVar, tRcvr))
              }
              (Implies(lhs, IsPositive(totalPerms)), Option.when(withExp)(perms.IsPositive(ast.CurrentPerm(fa)(fa.pos, fa.info, fa.errT))(fa.pos, fa.info, fa.errT)), s3)
            }
          v.decider.assert(permCheck) {
            case false =>
              createFailure(ve, v, s3, permCheck, permCheckExp)
            case true =>
              val smLookup = Lookup(fa.field.name, sm, tRcvr)
              val fr2 =
                s3.functionRecorder.recordSnapshot(fa, v.decider.pcs.branchConditions, smLookup)
              val s4 = s3.copy(functionRecorder = fr2)
              Q(s4, smLookup, v)
          }
      }
    } else {
      val resource = fa.res(s.program)
      chunkSupporter.lookup(s, s.h, resource, Seq(tRcvr), Option.when(withExp)(Seq(eRcvr.get)), ve, v)((s2, h2, tSnap, v2) => {
        val fr = s2.functionRecorder.recordSnapshot(fa, v2.decider.pcs.branchConditions, tSnap)
        val s3 = s2.copy(h = h2, functionRecorder = fr)
        Q(s3, tSnap, v)
      })
    }
  }

  def triggerResourceIfNeeded(s: State,
                              resAcc: ast.ResourceAccess,
                              tArgs: Seq[Term],
                              eArgs: Option[Seq[ast.Exp]],
                              v: Verifier): State = {
    if (s.isUsedAsTrigger(resAcc.res(s.program))) {
      val resource = resAcc.res(s.program)
      val chunkId = ChunkIdentifier(resource, s.program)
      val tFormalArgs = s.getFormalArgVars(resource, v)
      val name = resAcc match {
        case l: ast.LocationAccess =>
          val res = l.loc(s.program)
          res.name
        case w: ast.MagicWand =>
          val mwi = MagicWandIdentifier(w, s.program)
          mwi.toString
      }
      val trigger = (sm: Term) => ResourceTriggerFunction(resource, sm, tArgs, s.program)
      val (relevantChunks, _) =
        quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](s.h, chunkId)
      val (smDef1, smCache1) =
        quantifiedChunkSupporter.summarisingSnapshotMap(
          s, resource, tFormalArgs, relevantChunks, v)
      val eArgsStr = eArgs.mkString(", ")
      val debugExp = Option.when(withExp)(DebugExp.createInstance(Some(s"Resource trigger(${name}($eArgsStr))"), Some(resAcc),
        Some(resAcc), None, isInternal_ = true, InsertionOrderedSet.empty))
      v.decider.assume(trigger(smDef1.sm), debugExp)
      s.copy(smCache = smCache1, functionRecorder = s.functionRecorder.recordFvfAndDomain(smDef1))
    } else {
      s
    }
  }

  def produceSingle(s: State,
                    resource: ast.Resource,
                    tArgs: Seq[Term],
                    eArgs: Option[Seq[ast.Exp]],
                    tSnap: Term,
                    eSnap: Option[ast.Exp],
                    tPerm: Term,
                    ePerm: Option[ast.Exp],
                    pve: PartialVerificationError,
                    mergeAndTrigger: Boolean,
                    v: Verifier)
                   (Q: (State, Verifier) => VerificationResult) : VerificationResult = {
    val useQPs = s.isQuantifiedResource(resource)
    if (useQPs) {
      val trigger = (sm: Term) => ResourceTriggerFunction(resource, sm, tArgs, s.program)
      val tFormalArgs = s.getFormalArgVars(resource, v)
      val eFormalArgs = Option.when(withExp)(s.getFormalArgDecls(resource))
      quantifiedChunkSupporter.produceSingleLocation(
        s, resource, tFormalArgs, eFormalArgs, tArgs, eArgs, tSnap, tPerm, ePerm, trigger, mergeAndTrigger, v)(Q)
    } else {
      resource match {
        case w: ast.MagicWand =>
          magicWandSupporter.createChunk(s, w, MagicWandSnapshot(tSnap), pve, v)((s2, chWand, v2) =>
            chunkSupporter.produce(s2, s2.h, chWand, v2)((s3, h3, v3) =>
              Q(s3.copy(h = h3), v3)))
        case _ =>
          val chunkId = ChunkIdentifier(resource, s.program)
          val (resId, snap1) = if (resource.isInstanceOf[ast.Field]) (FieldID, tSnap) else (PredicateID, tSnap.convert(sorts.Snap))
          val ch = BasicChunk(resId, chunkId.asInstanceOf[BasicChunkIdentifier], tArgs, eArgs, snap1, eSnap, tPerm, ePerm)
          if (mergeAndTrigger) {
            chunkSupporter.produce(s, s.h, ch, v)((s2, h2, v2) => {
              if (resource.isInstanceOf[ast.Predicate] && Verifier.config.enablePredicateTriggersOnInhale() && s2.functionRecorder == NoopFunctionRecorder
                && !Verifier.config.disableFunctionUnfoldTrigger()) {
                val predicate = resource.asInstanceOf[ast.Predicate]
                val argsString = eArgs.mkString(", ")
                val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($argsString))", isInternal_ = true))
                v2.decider.assume(App(s2.predicateData(predicate.name).triggerFunction, snap1 +: tArgs), debugExp)
              }
              Q(s2.copy(h = h2), v2)
            })
          } else {
            Q(s.copy(h = s.h + ch), v)
          }
      }
    }
  }

  def consumeSingle(s: State,
                    h: Heap,
                    resAcc: ast.ResourceAccess,
                    tArgs: Seq[Term],
                    eArgs: Option[Seq[ast.Exp]],
                    tPerm: Term,
                    ePerm: Option[ast.Exp],
                    returnSnap: Boolean,
                    pve: PartialVerificationError,
                    v: Verifier)
                   (Q: (State, Heap, Option[Term], Verifier) => VerificationResult): VerificationResult = {
    val resource = resAcc.res(s.program)
    val useQPs = s.isQuantifiedResource(resource)
    if (useQPs) {
      val tFormalArgs = s.getFormalArgVars(resource, v)
      val eFormalArgs = Option.when(withExp)(s.getFormalArgDecls(resource))
      quantifiedChunkSupporter.consumeSingleLocation(
        s, h, tFormalArgs, eFormalArgs, tArgs, eArgs, resAcc, tPerm, ePerm, returnSnap, None, pve, v)(Q)
    } else {
      val ve = resAcc match {
        case l: ast.LocationAccess => pve dueTo InsufficientPermission(l)
        case w: ast.MagicWand => pve dueTo MagicWandChunkNotFound(w)
      }
      val description = s"consume ${resAcc.pos}: $resAcc"
      chunkSupporter.consume(s, h, resource, tArgs, eArgs, tPerm, ePerm, returnSnap, ve, v, description)(Q)
    }
  }

  def produceQuantified(s: State,
                        sf: (Sort, Verifier) => Term,
                        forall: ast.Forall,
                        resource: ast.Resource,
                        qvars: Seq[Var],
                        qvarExps: Option[Seq[ast.LocalVarDecl]],
                        tFormalArgs: Seq[Var],
                        eFormalArgs: Option[Seq[ast.LocalVarDecl]],
                        qid: String,
                        optTrigger: Option[Seq[ast.Trigger]],
                        tTriggers: Seq[Trigger],
                        auxGlobals: Seq[Term],
                        auxNonGlobals: Seq[Quantification],
                        auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        tCond: Term,
                        eCond: Option[ast.Exp],
                        tArgs: Seq[Term],
                        eArgs: Option[Seq[ast.Exp]],
                        tPerm: Term,
                        ePerm: Option[ast.Exp],
                        pve: PartialVerificationError,
                        negativePermissionReason: => ErrorReason,
                        notInjectiveReason: => ErrorReason,
                        v: Verifier)
                        (Q: (State, Verifier) => VerificationResult): VerificationResult = {
    val tSnap = resource match {
      case f: ast.Field =>
        sf(sorts.FieldValueFunction(v.snapshotSupporter.optimalSnapshotSort(f, s, v), f.name), v)
      case p: ast.Predicate =>
        sf(sorts.PredicateSnapFunction(s.predicateSnapMap(p.name), p.name), v)
      case _: ast.MagicWand =>
        sf(sorts.PredicateSnapFunction(sorts.Snap, qid), v)
    }

    quantifiedChunkSupporter.produce(
      s,
      forall,
      resource,
      qvars,
      qvarExps,
      tFormalArgs,
      eFormalArgs,
      qid,
      optTrigger,
      tTriggers,
      auxGlobals,
      auxNonGlobals,
      auxGlobalsExp,
      auxNonGlobalsExp,
      tCond,
      eCond,
      tArgs,
      eArgs,
      tSnap,
      tPerm,
      ePerm,
      pve,
      negativePermissionReason,
      notInjectiveReason,
      v
    )(Q)
  }

  def consumeQuantified(s: State,
                        h: Heap,
                        resource: ast.Resource,
                        qvars: Seq[Var],
                        qvarExps: Option[Seq[ast.LocalVarDecl]],
                        tFormalArgs: Seq[Var],
                        eFormalArgs: Option[Seq[ast.LocalVarDecl]],
                        qid: String,
                        optTrigger: Option[Seq[ast.Trigger]],
                        tTriggers: Seq[Trigger],
                        auxGlobals: Seq[Term],
                        auxNonGlobals: Seq[Quantification],
                        auxGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        auxNonGlobalsExp: Option[InsertionOrderedSet[DebugExp]],
                        tCond: Term,
                        eCond: Option[ast.Exp],
                        tArgs: Seq[Term],
                        eArgs: Option[Seq[ast.Exp]],
                        tPerm: Term,
                        ePerm: Option[ast.Exp],
                        returnSnap: Boolean,
                        pve: PartialVerificationError,
                        negativePermissionReason: => ErrorReason,
                        notInjectiveReason: => ErrorReason,
                        insufficientPermissionReason: => ErrorReason,
                        v: Verifier)
                       (Q: (State, Heap, Option[Term], Verifier) => VerificationResult): VerificationResult = {
    quantifiedChunkSupporter.consume(
      s,
      h,
      resource,
      qvars,
      qvarExps,
      tFormalArgs,
      eFormalArgs,
      qid,
      optTrigger,
      tTriggers,
      auxGlobals,
      auxNonGlobals,
      auxGlobalsExp,
      auxNonGlobalsExp,
      tCond,
      eCond,
      tArgs,
      eArgs,
      tPerm,
      ePerm,
      returnSnap,
      pve,
      negativePermissionReason,
      notInjectiveReason,
      insufficientPermissionReason,
      v
    )(Q)
  }

  def havocResource(s: State,
                    lhs: Term,
                    resource: ast.Resource,
                    condInfo: HavocHelperData,
                    v: Verifier): Heap = {
    if (s.isQuantifiedResource(resource)) {
      havocQuantifiedResource(s, lhs, resource, condInfo, v)
    } else {
      havocNonQuantifiedResource(s, lhs, resource, condInfo, v)
    }
  }

  /** Havoc a non-quantified resource. This helper function is used by havoc and havocall.
    * Suppose we want to havoc a resource R(e1, ..., en).
    * We filter the heap to only consider chunks with R. For each chunk R(vars; s, p), we
    * replace it with R(vars; s', p) where s' := ite(cond, fresh, s).
    * `cond` is calculated using `condInfo` by a helper function
    *
    * @param s        the state
    * @param lhs      the havoc condition
    * @param resource the type of resource we are havocking
    * @param condInfo the info needed to calculate the snapshot replace condition
    * @param v        the verifier
    * @return the resulting heap
    */
  private def havocNonQuantifiedResource(s: State,
                                         lhs: Term,
                                         resource: ast.Resource,
                                         condInfo: HavocHelperData,
                                         v: Verifier)
  : Heap = {

    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, otherChunks) = chunkSupporter.splitHeap[NonQuantifiedChunk](s.h, id)

    val newChunks = relevantChunks.map {
      case ch: MagicWandChunk =>
        val havockedSnap = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction, Option.when(withExp)(PUnknown()))
        val cond = replacementCond(lhs, ch.args, condInfo)
        val magicWandSnapshot = MagicWandSnapshot(Ite(cond, havockedSnap, ch.snap.mwsf))
        ch.withSnap(magicWandSnapshot, None)

      case ch =>
        val havockedSnap = freshSnap(ch.snap.sort, v)
        val cond = replacementCond(lhs, ch.args, condInfo)
        ch.withSnap(Ite(cond, havockedSnap, ch.snap), None)
    }
    Heap(otherChunks ++ newChunks)
  }

  /** Havoc a quantified resource. This helper function is used by havoc and havocall.
    * Suppose we want to havoc a resource R(r1, ..., rn).
    * We filter the heap to only consider chunks with R. For each chunk R(rs; sm, pm), we
    * replace it with R(rs; sm', pm)
    * We axiomatize the new snapshot map sm' as follows:
    * forall rs :: !cond(rs) ==> sm(rs) == sm'(rs)
    * the snapshot replacement condition `cond` is calculated by a helper function
    * This axiomatization provides no information about values which satisfy the snapshot
    * replacement condition, thus these snapshots are in essence, havocked.
    *
    * @param s        the state
    * @param lhs      the havoc condition
    * @param resource the resource type that we will havoc
    * @param condInfo the info needed to calculate the snapshot replace function
    * @param v        the verifier
    * @return the resulting heap
    */
  private def havocQuantifiedResource(s: State,
                                      lhs: Term,
                                      resource: ast.Resource,
                                      condInfo: HavocHelperData,
                                      v: Verifier) : Heap = {

    // Quantified field chunks are of the form R(r; sm, pm).
    // Conceptually, quantified predicate/wand chunks look like R(r1, ..., rn; sm, pm).
    // However, they are implemented as R(s; sm, pm). Thus, the snapshot map and permission
    // map take this aggregated quantifier s as input.
    // The arguments can be accessed via the snapshot destructors First and Second, e.g.
    //  r1 = First(s),
    //  r2 = First(Second(s)),
    //  ...
    val aggregateQvar = resource match {
      case _: ast.Field => `?r`
      case _ => `?s`
    }

    // Get the sequence of quantified variables (r1, ..., rn). For fields, this is the same
    // as aggregateQVar.
    val codomainQVars = s.getFormalArgVars(resource, v)

    val cond = replacementCond(lhs, codomainQVars, condInfo)

    // The condition is in terms of (r1, ..., rn). We must write it in terms of s.
    // Create the map from codomainQVars to expressions on the aggregateQVar, e.g.
    // r1 -> First(s), r2 -> First(Second(s)), etc.
    // Use this to rewrite cond in terms of s
    val codomainToAggregate = codomainQVars.zip(fromSnapTree(aggregateQvar, codomainQVars)).to(silicon.Map)
    val transformedCond = cond.replace(codomainToAggregate)

    val id = ChunkIdentifier(resource, s.program)
    val (relevantChunks, otherChunks) = quantifiedChunkSupporter.splitHeap[QuantifiedBasicChunk](s.h, id)

    val newChunks = relevantChunks.map { ch =>

      // Create a fresh snapshot map that we will axiomatize.
      // The argument additionalFvfArgs is an empty list because havocall statements cannot
      // be nested inside of quantifiers, thus it is impossible for us to be in a setting
      // with additional quantified variables.
      val newSm = freshSnapshotMap(s, resource, List(), v)

      // axiomatize the snapshot map:
      //  forall s: Snap :: !cond(s) ==> sm(s) == sm'(s)
      val lookupNew = ResourceLookup(resource, newSm, Seq(aggregateQvar), s.program)
      val lookupOld = ResourceLookup(resource, ch.snapshotMap, Seq(aggregateQvar), s.program)
      val newAxiom = Forall(
        aggregateQvar,
        Implies(Not(transformedCond), lookupOld === lookupNew),
        Seq(Trigger(lookupNew), Trigger(lookupOld)),
        s"qp.smValDef${v.counter(this).next()}",
        isGlobal = true, // TODO: should the quantifier be global? Matches example in summarize_field
      )

      v.decider.prover.comment("axiomatized snapshot map after havoc")
      val debugExp = Option.when(withExp)(DebugExp.createInstance("havoc new axiom", isInternal_ = true))
      v.decider.assume(newAxiom, debugExp)

      ch.withSnapshotMap(newSm)
    }
    Heap(newChunks ++ otherChunks)
  }

  /** Construct the condition that determines if we should replace a snapshot.
    * If we have havoc lhs ==> R(e1, ..., en) and we encounter the chunk R(r1, ..., rn; _, _),
    * then we should replace the snapshot if
    * cond := lhs && e1 == r1 && ... && en == rn
    * If we have havocall vs :: lhs(vs) ==> R(e1(vs), ..., en(vs)), then we assume that
    * e' is the inverse of the function (vs --> (e1(vs), ..., en(vs))).
    * If we encounter the chunk R(r1, ..., rn; _, _), then we should replace the snapshot if
    * cond := lhs(e'(e1(vs), ..., en(vs)))
    *
    * @param lhs       the havoc condition
    * @param chunkArgs the arguments to the chunk (r1, ..., rn)
    * @param condInfo  contains enough information to construct the snapshot replacement condition.
    *                  For havoc statements, it contains the variables (e1, ..., en)
    *                  For havocall statements, it contains the inverse function e'
    * @return the snapshot replacement condition
    */
  private def replacementCond(lhs: Term, chunkArgs: Seq[Term], condInfo: HavocHelperData): Term = {
    condInfo match {
      case HavocOneData(args) =>
        val eqs = And(chunkArgs.zip(args).map { case (t1, t2) => t1 === t2 })
        And(lhs, eqs)
      case HavocallData(inverseFunctions, codomainQVars, imagesOfCodomain) =>
        val replaceMap = inverseFunctions.qvarsToInversesOf(chunkArgs)
        And(lhs.replace(replaceMap), And(imagesOfCodomain.map(_.replace(codomainQVars, chunkArgs))))
    }
  }

  def collectForPermConditions(s: State,
                               resource: ast.Resource,
                               qVars: Seq[(Var, ast.LocalVar)],
                               tArgs: Seq[Term],
                               eArgs: Option[Seq[ast.Exp]]): Seq[(Term, (ast.Exp, Option[ast.Exp]), Seq[Var], Store, Seq[Trigger])] = {
    val usesQPChunks = s.isQuantifiedResource(resource)
    val resIdent = ChunkIdentifier(resource, s.program)
    val tVars = qVars map (_._1)
    if (usesQPChunks) {
      val chs = s.h.values.collect { case ch: QuantifiedBasicChunk if ch.id == resIdent => ch }
      chs.map { ch =>
        val bc = IsPositive(ch.perm.replace(ch.quantifiedVars, tArgs))
        val bcExp: ast.Exp = ast.LocalVar("chunk has non-zero permission", ast.Bool)() // TODO
        val bcExpNew = Option.when(withExp)(ast.GeCmp(replaceVarsInExp(ch.permExp.get, ch.quantifiedVarExps.get.map(_.name), eArgs.get), ast.NoPerm()())(ch.permExp.get.pos, ch.permExp.get.info, ch.permExp.get.errT))
        val tTriggers = Seq(Trigger(ch.valueAt(tArgs)))

        val trig = ch match {
          case fc: QuantifiedFieldChunk => FieldTrigger(fc.id.name, fc.fvf, tArgs.head)
          case pc: QuantifiedPredicateChunk => PredicateTrigger(pc.id.name, pc.psf, tArgs)
          case wc: QuantifiedMagicWandChunk => PredicateTrigger(wc.id.toString, wc.wsf, tArgs)
        }
        (And(trig, bc), (bcExp, bcExpNew), tVars, Store(), tTriggers)
      }.toSeq
    } else {
      val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](s.h.values, resIdent)
      chs.map { ch =>
        val argsEqual = tArgs.zip(ch.args)
        val qvarDefs = qVars.map(v => argsEqual.find(_._1 == v._1).get)
        val qvarDefMap = silicon.Map.from(qvarDefs)
        val addedStore = Store(qVars.map(v => (v._2, (argsEqual.find(_._1 == v._1).get._2, None))))
        val argsEqualFiltered = argsEqual.filter(ae => !qvarDefs.contains(ae))
        val argsEqualSubst = argsEqualFiltered.map(ae => ae._1.replace(qvarDefMap) === ae._2)
        val cond = And(argsEqualSubst :+ IsPositive(ch.perm))

        val lhsExp: ast.Exp = ast.LocalVar("chunk matches forperm pattern and has positive permission", ast.Bool)() // TODO

        val lhsExpNew = if (withExp) {
          val argsEqualExps = (eArgs.get zip ch.argsExp.get) map (ae => ast.EqCmp(ae._1, ae._2)())
          val permExp = ch.permExp.get
          val isPositiveExpNew = ast.GeCmp(permExp, ast.NoPerm()())(permExp.pos, permExp.info, permExp.errT)
          val lhsExpNew = BigAnd(argsEqualExps :+ isPositiveExpNew)
          Some(lhsExpNew)
        } else {
          None
        }
        (cond, (lhsExp, lhsExpNew), Seq(), addedStore, Seq())
      }.toSeq
    }
  }

  def getEmptyHeap(program: ast.Program): Heap = {
    Heap()
  }
}

object defaultHeapSupporter extends DefaultHeapSupportRules
