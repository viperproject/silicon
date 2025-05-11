// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.{BasicChunkIdentifier, QuantifiedFieldChunk, State}
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.VerificationError


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

  //def execFieldAssign(s: State,
  //                    fa: ast.FieldAccess,
  //                    rhs: ast.Exp,
  //                    v: Verifier)
  //                   (Q: (State, Verifier) => VerificationResult)
  //: VerificationResult

  //def triggerPredicate()

  //def getCurrentPermAmount()

  //def consumeSingle()

  //def consumeQuantified()

  //def produceSingle()

  //def produceQuantified()

  //def havocSingle()

  //def havocQuantified()

  // def getEmptyHeap()

}

class DefaultHeapSupporter extends HeapSupportRules {
  import evaluator._

  def isPossibleTrigger(s: State, fa: ast.FieldAccess): Boolean = {
    s.qpFields.contains(fa.field)
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

}

object defaultHeapSupporter extends DefaultHeapSupporter
