// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.VerificationResult
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, ChunkIdentifier, Heap, Identifier, MagicWandChunk, MagicWandIdentifier, QuantifiedFieldChunk, QuantifiedPredicateChunk, State}
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.reasons.InsufficientPermission
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

  def addToHeap(s: State,
                h: Heap,
                resource: ast.Resource,
                tArgs: Seq[Term],
                eArgs: Option[Seq[ast.Exp]],
                tSnap: Term,
                eSnap: Option[ast.Exp],
                tPerm: Term,
                ePerm: Option[ast.Exp],
                v: Verifier)
                : Heap

  def triggerPredicate(s: State,
                       pa: ast.PredicateAccess,
                       tArgs: Seq[Term],
                       eArgs: Option[Seq[ast.Exp]],
                       v: Verifier)
                       : State

  //def triggerPredicate()

  //def getCurrentPermAmount()

  //def consumeSingle()

  //def consumeQuantified()

  def produceSingle(s: State,
                    resource: ast.Resource,
                    tArgs: Seq[Term],
                    eArgs: Option[Seq[ast.Exp]],
                    tSnap: Term,
                    eSnap: Option[ast.Exp],
                    tPerm: Term,
                    ePerm: Option[ast.Exp],
                    pve: PartialVerificationError,
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

  //def havocSingle()

  //def havocQuantified()

  // def getEmptyHeap()

}

class DefaultHeapSupporter extends HeapSupportRules {
  import evaluator._

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
      val s2 = if (s.heapDependentTriggers.contains(field)) {
        val (smDef1, smCache1) =
          quantifiedChunkSupporter.summarisingSnapshotMap(
            s, field, Seq(`?r`), relevantChunks, v)
        val debugExp = Option.when(withExp)(DebugExp.createInstance(s"Field Trigger: (${eRcvrNew.toString()}).${field.name}"))
        v.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr), debugExp)
        s.copy(smCache = smCache1)
      } else {
        s
      }
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
          if (relevantChunks.size == 1) {
            // No need to create a summary since there is only one chunk to look at.
            if (s.heapDependentTriggers.contains(fa.field)) {
              val trigger = FieldTrigger(fa.field.name, relevantChunks.head.fvf, tRcvr)
              val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
              v.decider.assume(trigger, triggerExp)
            }
            val (permCheck, permCheckExp, s1a) =
              if (s.triggerExp) {
                (True, Option.when(withExp)(ast.TrueLit()()), s)
              } else {
                val (s1a, lhs) = tRcvr match {
                  case _: Literal | _: Var => (s, True)
                  case _ =>
                    // Make sure the receiver exists on the SMT level and is thus able to trigger any relevant quantifiers.
                    val rcvrVar = v.decider.appliedFresh("rcvr", tRcvr.sort, s.relevantQuantifiedVariables.map(_._1))
                    val newFuncRec = s.functionRecorder.recordFreshSnapshot(rcvrVar.applicable.asInstanceOf[Function])
                    (s.copy(functionRecorder = newFuncRec), BuiltinEquals(rcvrVar, tRcvr))
                }
                val permVal = relevantChunks.head.perm
                val totalPermissions = permVal.replace(relevantChunks.head.quantifiedVars, Seq(tRcvr))
                (Implies(lhs, IsPositive(totalPermissions)), Option.when(withExp)(perms.IsPositive(ast.CurrentPerm(fa)(fa.pos, fa.info, fa.errT))(fa.pos, fa.info, fa.errT)), s1a)
              }
            v.decider.assert(permCheck) {
              case false =>
                createFailure(ve, v, s1a, permCheck, permCheckExp)
              case true =>
                val smLookup = Lookup(fa.field.name, relevantChunks.head.fvf, tRcvr)
                val fr2 =
                  s1a.functionRecorder.recordSnapshot(fa, v.decider.pcs.branchConditions, smLookup)
                val s2 = s1a.copy(functionRecorder = fr2)
                Q(s2, smLookup, v)
            }
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
            if (s2.heapDependentTriggers.contains(fa.field)) {
              val trigger = FieldTrigger(fa.field.name, smDef1.sm, tRcvr)
              val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
              v.decider.assume(trigger, triggerExp)
            }
            val (permCheck, permCheckExp) =
              if (s2.triggerExp) {
                (True, Option.when(withExp)(ast.TrueLit()()))
              } else {
                val totalPermissions = PermLookup(fa.field.name, pmDef1.pm, tRcvr)
                (IsPositive(totalPermissions), Option.when(withExp)(ast.PermGtCmp(ast.CurrentPerm(fa)(fa.pos, fa.info, fa.errT), ast.NoPerm()())(fa.pos, fa.info, fa.errT)))
              }
            v.decider.assert(permCheck) {
              case false =>
                createFailure(ve, v, s2, permCheck, permCheckExp)
              case true =>
                val smLookup = Lookup(fa.field.name, smDef1.sm, tRcvr)
                val fr2 =
                  s2.functionRecorder.recordSnapshot(fa, v.decider.pcs.branchConditions, smLookup)
                    .recordFvfAndDomain(smDef1)
                val s3 = s2.copy(functionRecorder = fr2)
                Q(s3, smLookup, v)
            }
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

  def addToHeap(s: State,
                h: Heap,
                resource: ast.Resource,
                tArgs: Seq[Term],
                eArgs: Option[Seq[ast.Exp]],
                tSnap: Term,
                eSnap: Option[ast.Exp],
                tPerm: Term,
                ePerm: Option[ast.Exp],
                v: Verifier)
                : Heap = {
    val useQPs = resource match {
      case f: ast.Field => s.qpFields.contains(f)
      case p: ast.Predicate => s.qpPredicates.contains(p)
      case w: ast.MagicWand => s.qpMagicWands.contains(MagicWandIdentifier(w, s.program))
    }
    val newChunk = if (useQPs) {
      val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, resource, tArgs, tSnap, v)
      v.decider.prover.comment("Definitional axioms for singleton-FVF's value")
      val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-FVF's value", isInternal_ = true))
      v.decider.assumeDefinition(smValueDef, debugExp)
      val (formalVars, formalVarsExp) = resource match {
        case _: ast.Field =>
          (Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)())))
        case p: ast.Predicate =>
          (s.predicateFormalVarMap(p), Option.when(withExp)(p.formalArgs))
        case w: ast.MagicWand =>
          val bodyVars = w.subexpressionsToEvaluate(s.program)
          val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
          val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
          (formalVars, formalVarExps)
      }
      quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, formalVarsExp, resource, tArgs, eArgs, tPerm, ePerm, sm, s.program)
    } else {
      resource match {
        case w: ast.MagicWand =>
          MagicWandChunk(MagicWandIdentifier(w, s.program), ???, tArgs, eArgs, ???, tPerm, ePerm)
        case l: ast.Location =>
          BasicChunk(FieldID, BasicChunkIdentifier(l.name), tArgs, eArgs, tSnap, eSnap, tPerm, ePerm)
      }
    }
    h + Heap(Seq(newChunk))
  }

  def triggerPredicate(s: State,
                       pa: ast.PredicateAccess,
                       tArgs: Seq[Term],
                       eArgs: Option[Seq[ast.Exp]],
                       v: Verifier)
                       : State = {
    val predicate = pa.loc(s.program)
    if (s.qpPredicates.contains(predicate)) {
      val (relevantChunks, _) =
        quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s.h, BasicChunkIdentifier(predicate.name))
      val (smDef1, smCache1) =
        quantifiedChunkSupporter.summarisingSnapshotMap(
          s, predicate, s.predicateFormalVarMap(predicate), relevantChunks, v)
      val eArgsStr = eArgs.mkString(", ")
      val debugExp = Option.when(withExp)(DebugExp.createInstance(Some(s"PredicateTrigger(${predicate.name}($eArgsStr))"), Some(pa),
        Some(ast.PredicateAccess(eArgs.get, pa.predicateName)(pa.pos, pa.info, pa.errT)), None, isInternal_ = true, InsertionOrderedSet.empty))
      v.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs), debugExp)
      s.copy(smCache = smCache1)
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
                    v: Verifier)
                   (Q: (State, Verifier) => VerificationResult) : VerificationResult = {
    val useQPs = resource match {
      case f: ast.Field => s.qpFields.contains(f)
      case p: ast.Predicate => s.qpPredicates.contains(p)
      case w: ast.MagicWand => s.qpMagicWands.contains(MagicWandIdentifier(w, s.program))
    }
    if (useQPs) {
      val trigger = (sm: Term) => ResourceTriggerFunction(resource, sm, tArgs, s.program)
      val (tFormalArgs, eFormalArgs) = resource match {
        case _: ast.Field =>
          (Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)())))
        case p: ast.Predicate =>
          (s.predicateFormalVarMap(p), Option.when(withExp)(p.formalArgs))
        case w: ast.MagicWand =>
          val bodyVars = w.subexpressionsToEvaluate(s.program)
          val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
          val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
          (formalVars, formalVarExps)
      }
      quantifiedChunkSupporter.produceSingleLocation(
        s, resource, tFormalArgs, eFormalArgs, tArgs, eArgs, tSnap, tPerm, ePerm, trigger, v)(Q)
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
          chunkSupporter.produce(s, s.h, ch, v)((s2, h2, v2) => {
            if (resource.isInstanceOf[ast.Predicate] && Verifier.config.enablePredicateTriggersOnInhale() && s2.functionRecorder == NoopFunctionRecorder
              && !Verifier.config.disableFunctionUnfoldTrigger()) {
              val predicate = resource.asInstanceOf[ast.Predicate]
              val argsString = eArgs.mkString(", ")
              val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($argsString))", isInternal_ = true))
              v2.decider.assume(App(s2.predicateData(predicate).triggerFunction, snap1 +: tArgs), debugExp)
            }
            Q(s2.copy(h = h2), v2)
          })
      }
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
        sf(sorts.PredicateSnapFunction(s.predicateSnapMap(p), p.name), v)
      case _: ast.MagicWand =>
        sf(sorts.PredicateSnapFunction(sorts.Snap, qid), v)
    }
    val s1 = s.copy(constrainableARPs = s.constrainableARPs)
    quantifiedChunkSupporter.produce(
      s1,
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
}

object defaultHeapSupporter extends DefaultHeapSupporter
