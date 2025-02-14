// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.Config.JoinMode
import viper.silver.ast
import viper.silver.verifier.{CounterexampleTransformer, PartialVerificationError, VerifierWarning}
import viper.silver.verifier.errors.{ErrorWrapperWithExampleTransformer, PreconditionInAppFalse}
import viper.silver.verifier.reasons._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.interfaces.state.{ChunkIdentifer, NonQuantifiedChunk}
import viper.silicon.logger.records.data.{CondExpRecord, EvaluateRecord, ImpliesRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.implicits._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.ast._
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silicon.{Map, TriggerSets}
import viper.silver.ast.{AnnotationInfo, LocalVarWithVersion, TrueLit, WeightedQuantifier}
import viper.silver.reporter.{AnnotationWarning, WarningsDuringVerification}
import viper.silver.utility.Common.Rational


/* TODO: With the current design w.r.t. parallelism, eval should never "move" an execution
 *       to a different verifier. Hence, consider not passing the verifier to continuations
 *       of eval.
 */

trait EvaluationRules extends SymbolicExecutionRules {
  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Option[List[ast.Exp]], Verifier) => VerificationResult)
           : VerificationResult

  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
          : VerificationResult

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                        : VerificationResult

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp],
                     es2: Seq[ast.Exp],
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Seq[Var], Option[Seq[ast.LocalVarDecl]], Seq[Term], Option[Seq[ast.Exp]], Option[(Seq[Term], Option[Seq[ast.Exp]], Seq[Trigger], (Seq[Term], Seq[Quantification]), Option[(InsertionOrderedSet[DebugExp], InsertionOrderedSet[DebugExp])])], Verifier) => VerificationResult)
                    : VerificationResult
}

object evaluator extends EvaluationRules {
  import consumer._
  import producer._

  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Option[List[ast.Exp]], Verifier) => VerificationResult)
           : VerificationResult =

    evals2(s, es, Nil, pvef, v)(Q)

  private def evals2(s: State, es: Seq[ast.Exp], ts: List[Term], pvef: ast.Exp => PartialVerificationError, v: Verifier)
                    (Q: (State, List[Term], Option[List[ast.Exp]], Verifier) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(s, ts.reverse, if (withExp) Some(List.empty) else None, v)
    else
      eval(s, es.head, pvef(es.head), v)((s1, t, eNew, v1) =>
        evals2(s1, es.tail, t :: ts,  pvef, v1)((s2, ts2, es2, v2) => Q(s2, ts2, eNew.map(eN => eN :: es2.get), v2)))
  }

  /** Wrapper Method for eval, for logging. See Executor.scala for explanation of analogue. **/
  @inline
  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
          : VerificationResult = {

    val sepIdentifier = v.symbExLog.openScope(new EvaluateRecord(e, s, v.decider.pcs))
    eval3(s, e, pve, v)((s1, t, eNew, v1) => {
      v1.symbExLog.closeScope(sepIdentifier)
      Q(s1, t, eNew, v1)})
  }

  def eval3(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
           (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
           : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
            | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
            | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        v.logger.debug(s"\nEVAL ${viper.silicon.utils.ast.sourceLineColumn(e)}: $e")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.partiallyConsumedHeap.nonEmpty)
          v.logger.debug("pcH = " + s.partiallyConsumedHeap.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        s.oldHeaps.get(Verifier.MAGIC_WAND_LHS_STATE_LABEL) match {
          case Some(hLhs) =>   v.logger.debug("hLhs = " + v.stateFormatter.format(hLhs))
          case None =>
        }
        v.decider.prover.comment(s"[eval] $e")
    }

    /* Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * Also deactivate magic wand's recording of consumed and produced permissions: if the
     * evaluation to perform involves consuming or producing permissions, e.g. because of
     * an unfolding expression, these should not be recorded.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    eval2(s1, e, pve, v)((s2, t, eNew, v1) => {
      val s3 =
        if (s2.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (pt -> t))
            case fa: ast.FieldAccess if s2.qpFields.contains(fa.field) =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (fa -> t))
            case _ =>
              s2}
        else
          s2
      val s4 = s3.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s4, t, eNew, v1)})
  }

  protected def eval2(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
                     (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
                     : VerificationResult = {
    val eOpt = Option.when(withExp)(e)
    val resultTerm = e match {
      case _: ast.TrueLit => Q(s, True, eOpt, v)
      case _: ast.FalseLit => Q(s, False, eOpt, v)

      case _: ast.NullLit => Q(s, Null, eOpt, v)
      case ast.IntLit(bigval) => Q(s, IntLiteral(bigval), eOpt, v)

      case ast.EqCmp(e0, e1) => evalBinOp(s, e0, e1, Equals, pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, Option.when(withExp)(ast.EqCmp(e0New.get, e1New.get)(e.pos, e.info, e.errT)), v1))
      case ast.NeCmp(e0, e1) => evalBinOp(s, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, Option.when(withExp)(ast.NeCmp(e0New.get, e1New.get)(e.pos, e.info, e.errT)), v1))

      case x: ast.LocalVarWithVersion =>
        val sort = v.symbolConverter.toSort(x.typ)
        val term = Var(Identifier.apply(x.name + "@" + v.uniqueId), sort, false)
        Q(s, term, eOpt, v)

      case x: ast.AbstractLocalVar => Q(s, s.g(x), s.g.getExp(x), v)

      case _: ast.FullPerm => Q(s, FullPerm, eOpt, v)
      case _: ast.NoPerm => Q(s, NoPerm, eOpt, v)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOp(s, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, v)((s1, tFP, e0New, e1New, v1) =>
          failIfDivByZero(s1, tFP, e1, e1New, t1, predef.Zero, pve, v1)((s2, t, v2)
            => Q(s2, t, e0New.map(ast.FractionalPerm(_, e1New.get)(e.pos, e.info, e.errT)), v2)))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints, eVar) = v.decider.freshARP()
        val constraintExp = Option.when(withExp)(DebugExp.createInstance(s"${eVar.get.toString} > none", true))
        v.decider.assumeDefinition(tConstraints, constraintExp)
        /* TODO: Only record wildcards in State.constrainableARPs that are used in exhale
         *       position. Currently, wildcards used in inhale position (only) may not be removed
         *       from State.constrainableARPs (potentially inefficient, but should be sound).
         *
         *       Probably better in general: change evaluator signature such that, in addition to
         *       the resulting term, further data about the evaluation process (e.g. a mapping
         *       from expressions to terms, fresh wildcards, ...) is returned.
         *
         *       Alternative (for just wildcards): introduce WildcardPerm, extract them from the
         *       term returned by eval, mark as constrainable on client-side (e.g. in consumer).
         */
        val s1 =
          s.copy(functionRecorder = s.functionRecorder.recordConstrainedVar(tVar, tConstraints))
           .setConstrainable(Seq(tVar), true)
        Q(s1, tVar, eVar, v)

      case fa: ast.FieldAccess if s.qpFields.contains(fa.field) =>
        eval(s, fa.rcv, pve, v)((s1, tRcvr, eRcvr, v1) => {
          val (debugHeapName, debugLabel) = v1.getDebugOldLabel(s1, fa.pos)
          val newFa = Option.when(withExp)({
            if (s1.isEvalInOld) ast.FieldAccess(eRcvr.get, fa.field)(fa.pos, fa.info, fa.errT)
            else ast.DebugLabelledOld(ast.FieldAccess(eRcvr.get, fa.field)(), debugLabel)(fa.pos, fa.info, fa.errT)
          })
          val (relevantChunks, _) =
            quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s1.h, BasicChunkIdentifier(fa.field.name))
          s1.smCache.get((fa.field, relevantChunks)) match {
            case Some((fvfDef: SnapshotMapDefinition, totalPermissions)) if !Verifier.config.disableValueMapCaching() =>
              /* The next assertion must be made if the FVF definition is taken from the cache;
               * in the other case it is part of quantifiedChunkSupporter.withValue.
               */
              /* Re-emit definition since the previous definition could be nested under
               * an auxiliary quantifier (resulting from the evaluation of some Silver
               * quantifier in whose body field 'fa.field' was accessed)
               * which is protected by a trigger term that we currently don't have.
               */
              v1.decider.assume(And(fvfDef.valueDefinitions), Option.when(withExp)(DebugExp.createInstance("Value definitions", isInternal_ = true)))
              if (s1.heapDependentTriggers.contains(fa.field)){
                val trigger = FieldTrigger(fa.field.name, fvfDef.sm, tRcvr)
                val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
                v1.decider.assume(trigger, triggerExp)
              }
              if (s1.triggerExp) {
                val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup)
                val s2 = s1.copy(functionRecorder = fr1)
                val s3 = if (Verifier.config.enableDebugging() && !s2.isEvalInOld) s2.copy(oldHeaps = s2.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s2))) else s2
                Q(s3, fvfLookup, newFa, v1)
              } else {
                val toAssert = IsPositive(totalPermissions.replace(`?r`, tRcvr))
                v1.decider.assert(toAssert) {
                  case false =>
                    createFailure(pve dueTo InsufficientPermission(fa), v1, s1, toAssert, Option.when(withExp)(perms.IsPositive(ast.CurrentPerm(fa)())()))
                  case true =>
                    val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                    val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup).recordFvfAndDomain(fvfDef)
                    val possTriggers = if (s1.heapDependentTriggers.contains(fa.field) && s1.recordPossibleTriggers)
                      s1.possibleTriggers + (fa -> FieldTrigger(fa.field.name, fvfDef.sm, tRcvr))
                    else
                      s1.possibleTriggers
                    val s2 = s1.copy(functionRecorder = fr1, possibleTriggers = possTriggers)
                    val s3 = if (Verifier.config.enableDebugging() && !s2.isEvalInOld) s2.copy(oldHeaps = s2.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s2))) else s2
                    Q(s3, fvfLookup, newFa, v1)}
              }
            case _ =>
              if (relevantChunks.size == 1) {
                // No need to create a summary since there is only one chunk to look at.
                if (s1.heapDependentTriggers.contains(fa.field)) {
                  val trigger = FieldTrigger(fa.field.name, relevantChunks.head.fvf, tRcvr)
                  val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
                  v1.decider.assume(trigger, triggerExp)
                }
                val (permCheck, permCheckExp) =
                  if (s1.triggerExp) {
                    (True, Option.when(withExp)(TrueLit()()))
                  } else {
                    val permVal = relevantChunks.head.perm
                    val totalPermissions = permVal.replace(relevantChunks.head.quantifiedVars, Seq(tRcvr))
                    (IsPositive(totalPermissions), Option.when(withExp)(ast.PermGtCmp(ast.CurrentPerm(fa)(fa.pos, fa.info, fa.errT), ast.NoPerm()())(fa.pos, fa.info, fa.errT)))
                  }
                v1.decider.assert(permCheck) {
                  case false =>
                    createFailure(pve dueTo InsufficientPermission(fa), v1, s1, permCheck, permCheckExp)
                  case true =>
                    val smLookup = Lookup(fa.field.name, relevantChunks.head.fvf, tRcvr)
                    val fr2 =
                      s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, smLookup)
                    val s2 = s1.copy(functionRecorder = fr2)
                    Q(s2, smLookup, newFa, v1)
                }
              } else {
                val (s2, smDef1, pmDef1) =
                  quantifiedChunkSupporter.heapSummarisingMaps(
                    s = s1,
                    resource = fa.field,
                    codomainQVars = Seq(`?r`),
                    relevantChunks = relevantChunks,
                    optSmDomainDefinitionCondition = None,
                    optQVarsInstantiations = None,
                    v = v1)
                if (s2.heapDependentTriggers.contains(fa.field)) {
                  val trigger = FieldTrigger(fa.field.name, smDef1.sm, tRcvr)
                  val triggerExp = Option.when(withExp)(DebugExp.createInstance(s"FieldTrigger(${eRcvr.toString()}.${fa.field.name})"))
                  v1.decider.assume(trigger, triggerExp)
                }
                val (permCheck, permCheckExp) =
                  if (s2.triggerExp) {
                    (True, Option.when(withExp)(TrueLit()()))
                  } else {
                    val totalPermissions = PermLookup(fa.field.name, pmDef1.pm, tRcvr)
                    (IsPositive(totalPermissions), Option.when(withExp)(ast.PermGtCmp(ast.CurrentPerm(fa)(fa.pos, fa.info, fa.errT), ast.NoPerm()())(fa.pos, fa.info, fa.errT)))
                  }
                v1.decider.assert(permCheck) {
                  case false =>
                    createFailure(pve dueTo InsufficientPermission(fa), v1, s2, permCheck, permCheckExp)
                  case true =>
                    val smLookup = Lookup(fa.field.name, smDef1.sm, tRcvr)
                    val fr2 =
                      s2.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, smLookup)
                        .recordFvfAndDomain(smDef1)
                    val s3 = s2.copy(functionRecorder = fr2)
                    Q(s3, smLookup, newFa, v1)
                }
              }
              }})

      case fa: ast.FieldAccess =>
        evalLocationAccess(s, fa, pve, v)((s1, _, tArgs, eArgs, v1) => {
          val ve = pve dueTo InsufficientPermission(fa)
          val resource = fa.res(s.program)
          chunkSupporter.lookup(s1, s1.h, resource, tArgs, eArgs, ve, v1)((s2, h2, tSnap, v2) => {
            val fr = s2.functionRecorder.recordSnapshot(fa, v2.decider.pcs.branchConditions, tSnap)
            val s3 = s2.copy(h = h2, functionRecorder = fr)
            val (debugHeapName, debugLabel) = v2.getDebugOldLabel(s3, fa.pos)
            val newFa = Option.when(withExp)({
              if (s3.isEvalInOld) ast.FieldAccess(eArgs.get.head, fa.field)(e.pos, e.info, e.errT)
              else ast.DebugLabelledOld(ast.FieldAccess(eArgs.get.head, fa.field)(), debugLabel)(e.pos, e.info, e.errT)
            })
            val s4 = if (Verifier.config.enableDebugging() && !s3.isEvalInOld) s3.copy(oldHeaps = s3.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s3))) else s3
            Q(s4, tSnap, newFa, v1)
          })
        })

      case ast.Not(e0) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          Q(s1, Not(t0), e0New.map(ast.Not(_)(e.pos, e.info, e.errT)), v1))

      case ast.Minus(e0) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          Q(s1, Minus(0, t0), e0New.map(ast.Minus(_)(e.pos, e.info, e.errT)), v1))

      case ast.Old(e0) =>
        evalInOldState(s, Verifier.PRE_STATE_LABEL, e0, pve, v)((s1, t0, e0New, v1) =>
          Q(s1, t0, e0New.map(ast.Old(_)(e.pos, e.info, e.errT)), v1))

      case old@ast.DebugLabelledOld(e0, lbl) =>
        val heapName = if (lbl.contains("#"))
          lbl.substring(0, lbl.indexOf("#"))
        else
          lbl
        s.oldHeaps.get(heapName) match {
          case None =>
            createFailure(pve dueTo LabelledStateNotReached(ast.LabelledOld(e0, heapName)(old.pos, old.info, old.errT)), v, s, "labelled state reached")
          case _ =>
            evalInOldState(s, heapName, e0, pve, v)((s1, t0, _, v1) =>
              Q(s1, t0, Some(old), v1))
        }

      case old @ ast.LabelledOld(e0, lbl) =>
        s.oldHeaps.get(lbl) match {
          case None =>
            createFailure(pve dueTo LabelledStateNotReached(old), v, s, "labelled state reached")
          case _ =>
            evalInOldState(s, lbl, e0, pve, v)((s1, t0, e0New, v1) =>
              Q(s1, t0, e0New.map(ast.LabelledOld(_, lbl)(old.pos, old.info, old.errT)), v1))}

      case ast.Let(x, e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) => {
          val t = v1.decider.appliedFresh("letvar", v1.symbolConverter.toSort(x.typ), s1.relevantQuantifiedVariables.map(_._1))
          val debugExp = Option.when(withExp)(DebugExp.createInstance("letvar assignment", InsertionOrderedSet(DebugExp.createInstance(ast.EqCmp(x.localVar, e0)(), ast.EqCmp(x.localVar, e0New.get)()))))
          v1.decider.assumeDefinition(BuiltinEquals(t, t0), debugExp)
          val newFuncRec = s1.functionRecorder.recordFreshSnapshot(t.applicable.asInstanceOf[Function])
          val possibleTriggersBefore = if (s1.recordPossibleTriggers) s1.possibleTriggers else Map.empty
          eval(s1.copy(g = s1.g + (x.localVar, (t0, e0New)), functionRecorder = newFuncRec), e1, pve, v1)((s2, t2, e1New, v2) => {
            val newPossibleTriggers = if (s2.recordPossibleTriggers) {
              val addedTriggers = s2.possibleTriggers -- possibleTriggersBefore.keys
              val addedTriggersReplaced = addedTriggers.map(at => at._1.replace(x.localVar, e0) -> at._2)
              s2.possibleTriggers ++ addedTriggersReplaced
            } else {
              s2.possibleTriggers
            }
            Q(s2.copy(possibleTriggers = newPossibleTriggers), t2, e0New.map(ast.Let(x, _, e1New.get)(e.pos, e.info, e.errT)), v2)
          })
        })

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => And(t1, t2), pve, v)((s1, t, e0New, e1New, v1) =>
          Q(s1, t, e0New.map(ast.And(_, e1New.get)(e.pos, e.info, e.errT)), v1))

      /* Short-circuiting evaluation of AND */
      case ae @ ast.And(_, _) =>
        val flattened = flattenOperator(ae, {case ast.And(e0, e1) => Seq(e0, e1)})
        evalSeqShortCircuit(And, s, flattened, pve, v)(Q)


      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => Or(t1, t2), pve, v)((s1, t, e0New, e1New, v1) =>
          Q(s1, t, e0New.map(ast.Or(_, e1New.get)(e.pos, e.info, e.errT)), v1))

      /* Short-circuiting evaluation of OR */
      case oe @ ast.Or(_, _) =>
        val flattened = flattenOperator(oe, {case ast.Or(e0, e1) => Seq(e0, e1)})
        evalSeqShortCircuit(Or, s, flattened, pve, v)(Q)

      case implies @ ast.Implies(e0, e1) =>
        val impliesRecord = new ImpliesRecord(implies, s, v.decider.pcs, "Implies")
        val uidImplies = v.symbExLog.openScope(impliesRecord)
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          evalImplies(s1, t0, (e0, e0New), e1, implies.info == FromShortCircuitingAnd, pve, v1)((s2, t1, e1New, v2) => {
            v2.symbExLog.closeScope(uidImplies)
            val implExpP = e0New.map(ast.Implies(_, e1New.get)(e.pos, e.info, e.errT))
            Q(s2, t1, implExpP, v2)
          }))

      case condExp @ ast.CondExp(e0, e1, e2) =>
        val condExpRecord = new CondExpRecord(condExp, s, v.decider.pcs, "CondExp")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s1, v1)((s2, v2, QB) =>
            brancher.branch(s2.copy(parallelizeBranches = false), t0, (e0, e0New), v2)(
              (s3, v3) => eval(s3.copy(parallelizeBranches = s2.parallelizeBranches), e1, pve, v3)((s4, t4, e4, v4) => QB(s4, (t4, e4), v4)),
              (s3, v3) => eval(s3.copy(parallelizeBranches = s2.parallelizeBranches), e2, pve, v3)((s4, t4, e4, v4) => QB(s4, (t4, e4), v4)))
          )(entries => {
            /* TODO: If branch(...) took orElse-continuations that are executed if a branch is dead, then then
                comparisons with t0/Not(t0) wouldn't be necessary. */
            val (s2, result, resultExp) = entries match {
              case Seq(entry) => // One branch is dead
                (entry.s, entry.data._1, entry.data._2)
              case Seq(entry1, entry2) => // Both branches are alive
                val condExp = e0New.map(c => ast.CondExp(c, entry1.data._2.get, entry2.data._2.get)(e0.pos, e0.info, e0.errT))
                (entry1.s.merge(entry2.s), Ite(t0, entry1.data._1, entry2.data._1), condExp)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, (result, resultExp))
          })((s4, r, v3) => {
            val (t3, eNew) = r
            v3.symbExLog.closeScope(uidCondExp)
            Q(s4, t3, eNew, v3)
          }))

      /* Integers */

      case ast.Add(e0, e1) =>
        evalBinOp(s, e0, e1, Plus, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.Add(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.Sub(e0, e1) =>
        evalBinOp(s, e0, e1, Minus, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.Sub(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.Mul(e0, e1) =>
        evalBinOp(s, e0, e1, Times, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.Mul(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.Div(e0, e1) =>
        evalBinOp(s, e0, e1, Div, pve, v)((s1, tDiv, e0New, e1New, v1) =>
          failIfDivByZero(s1, tDiv, e1, e1New, tDiv.p1, 0, pve, v1)((s2, t, v2)
            => Q(s2, t, e0New.map(e0p => ast.Div(e0p, e1New.get)(e.pos, e.info, e.errT)), v2)))

      case ast.Mod(e0, e1) =>
        evalBinOp(s, e0, e1, Mod, pve, v)((s1, tMod, e0New, e1New, v1) =>
          failIfDivByZero(s1, tMod, e1, e1New, tMod.p1, 0, pve, v1)((s2, t, v2)
          => Q(s2, t, e0New.map(e0p => ast.Mod(e0p, e1New.get)(e.pos, e.info, e.errT)), v2)))

      case ast.LeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.LeCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.LtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.LtCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.GeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.GeCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.GtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.GtCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      /* Permissions */

      case ast.PermAdd(e0, e1) =>
        evalBinOp(s, e0, e1, PermPlus, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermAdd(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.PermSub(e0, e1) =>
        evalBinOp(s, e0, e1, PermMinus, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermSub(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.PermMinus(e0) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          Q(s1, PermMinus(NoPerm, t0), e0New.map(e0p => ast.PermMinus(e0p)(e.pos, e.info, e.errT)), v1))

      case ast.PermMul(e0, e1) =>
        evalBinOp(s, e0, e1, PermTimes, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermMul(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.DebugPermMin(e0, e1) =>
        evalBinOp(s, e0, e1, PermMin, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.DebugPermMin(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.IntPermMul(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, e1New, v2) =>
            Q(s2, IntPermTimes(t0, t1), e0New.map(e0p => ast.IntPermMul(e0p, e1New.get)(e.pos, e.info, e.errT)), v2)))

      case ast.PermDiv(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, e1New, v2) =>
            failIfDivByZero(s2, PermIntDiv(t0, t1), e1, e1New, t1, 0, pve, v2)((s3, t, v3)
              => Q(s3, t, e0New.map(e0p => ast.PermDiv(e0p, e1New.get)(e.pos, e.info, e.errT)), v3))))

      case ast.PermPermDiv(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, e1New, v2) =>
            failIfDivByZero(s2, PermPermDiv(t0, t1), e1, e1New, t1, FractionPermLiteral(Rational(0, 1)), pve, v2)((s3, t, v3) =>
              Q(s3, t, e0New.map(e0p => ast.PermPermDiv(e0p, e1New.get)(e.pos, e.info, e.errT)), v3))))

      case ast.PermLeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermLeCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.PermLtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermLtCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.PermGeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermGeCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.PermGtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)((s1, t, e0New, e1New, v1) => Q(s1, t, e0New.map(e0p => ast.PermGtCmp(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, m) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = v1.symbolConverter.toSort(dfa.typ)
          val fi = v1.symbolConverter.toFunction(s.program.findDomainFunction(funcName), inSorts :+ outSort, s.program)
          val dfaP = Option.when(withExp)(ast.DomainFuncApp(funcName, eArgsNew.get, m)(dfa.pos, dfa.info, dfa.typ, dfa.domainName, dfa.errT))
          Q(s1, App(fi, tArgs), dfaP, v1)})

      case bf @ ast.BackendFuncApp(funcName, eArgs) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) => {
          val func = s.program.findDomainFunction(funcName)
          val fi = v1.symbolConverter.toFunction(func, s.program)
          val bfP = Option.when(withExp)(ast.BackendFuncApp(funcName, eArgsNew.get)(bf.pos, bf.info, bf.typ, bf.interpretation, bf.errT))
          Q(s1, App(fi, tArgs), bfP, v1)})

      case ast.CurrentPerm(resacc) =>
        val h = s.partiallyConsumedHeap.getOrElse(s.h)
        evalResourceAccess(s, resacc, pve, v)((s1, identifier, args, eArgsNew, v1) => {
          val res = resacc.res(s.program)
          val eArgsString = eArgsNew.mkString(", ")
          /* It is assumed that, for a given field/predicate/wand identifier (res)
           * either only quantified or only non-quantified chunks are used.
           */
          val usesQPChunks = res match {
            case _: ast.MagicWand => s1.qpMagicWands.contains(identifier.asInstanceOf[MagicWandIdentifier])
            case field: ast.Field => s1.qpFields.contains(field)
            case pred: ast.Predicate => s1.qpPredicates.contains(pred)}
          val (s2, currentPermAmount) =
            if (usesQPChunks) {
              res match {
                case wand: ast.MagicWand =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h, identifier)
                  val bodyVars = wand.subexpressionsToEvaluate(s.program)
                  val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ), false))
                  val (s2, pmDef) = if (s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s1.program))) {
                    val (s2, smDef, pmDef) = quantifiedChunkSupporter.heapSummarisingMaps(s1, wand, formalVars, relevantChunks, v1)
                    val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${identifier.toString}($eArgsString))", isInternal_ = true))
                    v1.decider.assume(PredicateTrigger(identifier.toString, smDef.sm, args), debugExp)
                    (s2, pmDef)
                  } else {
                    val (pmDef, pmCache) =
                      quantifiedChunkSupporter.summarisingPermissionMap(
                        s1, wand, formalVars, relevantChunks, null, v1)

                    (s1.copy(pmCache = pmCache), pmDef)
                  }
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))

                case field: ast.Field =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](h, identifier)
                  val (s2, pmDef) = if (s1.heapDependentTriggers.contains(field)) {
                    val (s2, smDef, pmDef) = quantifiedChunkSupporter.heapSummarisingMaps(s1, field, Seq(`?r`), relevantChunks, v1)
                    val debugExp = Option.when(withExp)(DebugExp.createInstance(s"Field Trigger: ${eArgsNew.head}.${field.name}"))
                    v1.decider.assume(FieldTrigger(field.name, smDef.sm, args.head), debugExp)
                    (s2, pmDef)
                  } else {
                    val (pmDef, pmCache) =
                      quantifiedChunkSupporter.summarisingPermissionMap(
                        s1, field, Seq(`?r`), relevantChunks, null, v1)

                    (s1.copy(pmCache = pmCache), pmDef)
                  }
                  val currentPermAmount = PermLookup(field.name, pmDef.pm, args.head)
                  v1.decider.prover.comment(s"perm($resacc)  ~~>  assume upper permission bound")
                  val (debugHeapName, debugLabel) = v1.getDebugOldLabel(s2, resacc.pos, Some(h))
                  val exp = Option.when(withExp)(ast.PermLeCmp(ast.DebugLabelledOld(ast.CurrentPerm(resacc)(), debugLabel)(), ast.FullPerm()())())
                  v1.decider.assume(PermAtMost(currentPermAmount, FullPerm), exp, exp.map(s2.substituteVarsInExp(_)))
                  val s3 = if (Verifier.config.enableDebugging()) s2.copy(oldHeaps = s2.oldHeaps + (debugHeapName -> h)) else s2
                  (s3, currentPermAmount)

                case predicate: ast.Predicate =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h, identifier)
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(
                      s1, predicate, s1.predicateFormalVarMap(predicate), relevantChunks, v1)
                  if (s2.heapDependentTriggers.contains(predicate)){
                    val trigger = PredicateTrigger(predicate.name, smDef.sm, args)
                    val argsString = eArgsNew.mkString(", ")
                    v1.decider.assume(trigger, Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($argsString))", isInternal_ = true)))
                  }
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))
              }
            } else {
              val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
              val currentPermAmount =
                chs.foldLeft(NoPerm: Term)((q, ch) => {
                  val argsPairWiseEqual = And(args.zip(ch.args).map { case (a1, a2) => a1 === a2 })
                  PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm))
                })
              /* TODO: See todo above */
//              v1.decider.prover.comment(s"perm($locacc)  ~~>  assume upper permission bound")
//              v1.decider.prover.comment(perm.toString)
//              v1.decider.assume(PermAtMost(perm, FullPerm()))
              (s, currentPermAmount)
            }

          Q(s2, currentPermAmount, Option.when(withExp)(e), v1)})

      case ast.ForPerm(vars, resourceAccess, body) =>

        /* Iterate over the list of relevant chunks in continuation passing style (very similar
         * to evals), and evaluate the forperm-body with a different qvar assignment each time.
        */

        def bindRcvrsAndEvalBody(s: State, chs: Iterable[NonQuantifiedChunk], args: Seq[ast.Exp], ts: Seq[Term], es: Option[Seq[ast.Exp]], v: Verifier)
                                (Q: (State, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                                : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, es.map(_.reverse), v)
          else {
            val ch = chs.head

            val rcvrs = ch.args
            val rcvrsExp = ch.argsExp
            val s1 = s.copy()
            var g1 = s1.g
            var addCons : Seq[Term] = Seq()
            var addConsExp : Option[Seq[ast.Exp]] = Option.when(withExp)(Seq())
            for (vr <- vars) {
              if (args.contains(vr.localVar)) {
                val indices = args.zipWithIndex.filter(ai => ai._1 == vr.localVar).map(_._2)
                val index = indices.head
                g1 = g1 + (vr.localVar, (rcvrs(index), rcvrsExp.map(_(index))))
                if (indices.length > 1) {
                  val equalArgs = And(indices.tail map { i => rcvrs(i) === rcvrs(index) })
                  val equalArgsExp = Option.when(withExp)(BigAnd(indices.tail map { i => ast.EqCmp(rcvrsExp.get(i), rcvrsExp.get(index))() }))
                  addCons = addCons :+ equalArgs
                  addConsExp = addConsExp.map(_ :+ equalArgsExp.get)
                }
              }
            }
            val s2 = s1.copy(g1)

            val nonQuantArgs = args filter (a => !vars.map(_.localVar).contains(a))
            val indices = nonQuantArgs map (a => args.indexOf(a))

            // TODO LA: nonQuantArgs are not recorded yet
            val impliesRecord = new ImpliesRecord(null, s2, v.decider.pcs, "bindRcvrsAndEvalBody")
            val uidImplies = v.symbExLog.openScope(impliesRecord)

            evals(s2, nonQuantArgs, _ => pve, v)((s3, tArgs, eArgsNew, v1) => {
              val argsWithIndex = tArgs zip indices
              val zippedArgs = argsWithIndex map (ai => (ai._1, ch.args(ai._2)))
              val argsPairWiseEqual = And(zippedArgs map {case (a1, a2) => a1 === a2})

              val lhsExp: ast.Exp = ast.LocalVar("chunk matches forperm pattern and has positive permission", ast.Bool)() // TODO

              val lhsExpNew = if (withExp) {
                val argsWithIndexExpNew = eArgsNew.get zip indices
                val zippedArgsExpNew = argsWithIndexExpNew map (ai => (ai._1, ch.argsExp.get(ai._2)))
                val permExp = ch.permExp.get
                val isPositiveExpNew = ast.GeCmp(permExp, ast.NoPerm()())(permExp.pos, permExp.info, permExp.errT)
                val argsPairWiseEqualExpNew = BigAnd(zippedArgsExpNew map { case (a1, a2) => ast.EqCmp(a1, a2)() })
                val lhsExpNew = ast.CondExp(argsPairWiseEqualExpNew, BigAnd(addConsExp.get :+ isPositiveExpNew), ast.FalseLit()())()
                Some(lhsExpNew)
              } else {
                None
              }

              evalImplies(s3, Ite(argsPairWiseEqual, And(addCons :+ IsPositive(ch.perm)), False), (lhsExp, lhsExpNew), body, false, pve, v1) ((s4, tImplies, bodyNew, v2) =>{
                val eImpliesNew = lhsExpNew.map(ast.Implies(_, bodyNew.get)())
                bindRcvrsAndEvalBody(s4, chs.tail, args, tImplies +: ts, eImpliesNew.map(_ +: es.get), v2)((s5, ts1, es1, v3) => {
                  v3.symbExLog.closeScope(uidImplies)
                  Q(s5, ts1, es1, v3)
                })
              })
            })
          }
        }

        def bindQuantRcvrsAndEvalBody(s: State, chs: Iterable[QuantifiedBasicChunk], args: Seq[ast.Exp], ts: Seq[Term], es: Option[Seq[ast.Exp]], v: Verifier)
                                     (Q: (State, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                                     : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, es.map(_.reverse), v)
          else {
            val ch = chs.head

            val localVars = vars map (_.localVar)
            val varPair: Seq[(Var, ast.LocalVar)] = localVars map (x =>
              (v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ), Option.when(withExp)(extractPTypeFromExp(x))), x))
            val tVars = varPair map (_._1)
            val varsNew = Option.when(withExp)(varPair.map (tv => ast.LocalVarDecl(tv._1.id.name, tv._2.typ)(tv._2.pos, tv._2.info, tv._2.errT)))
            val termExpPair: Seq[(Term, Option[ast.Exp])] = varPair map (x =>
              (x._1.asInstanceOf[Term], Option.when(withExp)(LocalVarWithVersion(simplifyVariableName(x._1.id.name), x._2.typ)(x._2.pos, x._2.info, x._2.errT).asInstanceOf[ast.Exp])))
            val gVars = Store(localVars zip termExpPair)

            val s1 = s.copy(s.g + gVars, quantifiedVariables = varPair.map(v => v._1 -> Option.when(withExp)(v._2)) ++ s.quantifiedVariables)

            // TODO LA: args are not recorded yet
            val impliesRecord = new ImpliesRecord(null, s1, v.decider.pcs, "bindQuantRcvrsAndEvalBody")
            val uidImplies = v.symbExLog.openScope(impliesRecord)

            evals(s1, args, _ => pve, v)((s2, ts1, es1, v1) => {
              val bc = IsPositive(ch.perm.replace(ch.quantifiedVars, ts1))
              val bcExp: ast.Exp = ast.LocalVar("chunk has non-zero permission", ast.Bool)() // TODO
              val bcExpNew = Option.when(withExp)(ast.GeCmp(replaceVarsInExp(ch.permExp.get, ch.quantifiedVarExps.get.map(_.name), es1.get), ast.NoPerm()())(ch.permExp.get.pos, ch.permExp.get.info, ch.permExp.get.errT))
              val tTriggers = Seq(Trigger(ch.valueAt(ts1)))

              val trig = ch match {
                case fc: QuantifiedFieldChunk => FieldTrigger(fc.id.name, fc.fvf, ts1.head)
                case pc: QuantifiedPredicateChunk => PredicateTrigger(pc.id.name, pc.psf, ts1)
                case wc: QuantifiedMagicWandChunk => PredicateTrigger(wc.id.toString, wc.wsf, ts1)
              }

              evalImplies(s2, And(trig, bc), (bcExp, bcExpNew), body, false, pve, v1)((s3, tImplies, bodyNew, v2) => {
                val tQuant = Quantification(Forall, tVars, tImplies, tTriggers)
                val eQuantNew = Option.when(withExp)(ast.Forall(varsNew.get, Seq(), ast.Implies(bcExp, bodyNew.get)())())
                bindQuantRcvrsAndEvalBody(s3, chs.tail, args, tQuant +: ts, eQuantNew.map(_ +: es.get), v2)((s4, ts2, es2, v3) => {
                  v3.symbExLog.closeScope(uidImplies)
                  Q(s4, ts2, es2, v3)
                })})
            })
          }
        }

        val s1 = s.copy(h = s.partiallyConsumedHeap.getOrElse(s.h))

        val resIdent = ChunkIdentifier(resourceAccess.res(s.program), s.program)
        val args = resourceAccess match {
          case fa: ast.FieldAccess => Seq(fa.rcv)
          case pa: ast.PredicateAccess => pa.args
          case w: ast.MagicWand => w.subexpressionsToEvaluate(s.program)
        }
        val usesQPChunks = resourceAccess.res(s.program) match {
          case _: ast.MagicWand => s1.qpMagicWands.contains(resIdent.asInstanceOf[MagicWandIdentifier])
          case field: ast.Field => s1.qpFields.contains(field)
          case pred: ast.Predicate => s1.qpPredicates.contains(pred)
        }

        if (usesQPChunks) {
            val chs = s1.h.values.collect { case ch: QuantifiedBasicChunk if ch.id == resIdent => ch }
            bindQuantRcvrsAndEvalBody(s1, chs, args, Seq.empty, Option.when(withExp)(Seq.empty), v)((s2, ts, es, v1) => {
              val s3 = s2.copy(h = s.h, g = s.g)
              Q(s3, And(ts), Option.when(withExp)(BigAnd(es.get)), v1)
            })
        } else {
          val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](s1.h.values, resIdent)
          bindRcvrsAndEvalBody(s1, chs, args, Seq.empty, Option.when(withExp)(Seq.empty), v)((s2, ts, es, v1) => {
            val s3 = s2.copy(h = s.h, g = s.g)
            Q(s3, And(ts), Option.when(withExp)(BigAnd(es.get)), v1)
          })
        }

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            /* It is expected that quantifiers have already been provided with triggers,
             * either explicitly or by using a trigger generator.
             */
            (forall, Forall, forall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, exists.triggers)
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }
        val quantWeight = sourceQuant.info.getUniqueInfo[WeightedQuantifier] match {
          case Some(w) =>
            if (w.weight >= 0) {
              Some(w.weight)
            } else {
              v.reporter.report(AnnotationWarning(s"Invalid quantifier weight annotation: ${w}"))
              None
            }
          case None => sourceQuant.info.getUniqueInfo[AnnotationInfo] match {
            case Some(ai) if ai.values.contains("weight") =>
              ai.values("weight") match {
                case Seq(w) if w.toIntOption.exists(w => w >= 0) =>
                  Some(w.toInt)
                case s =>
                  v.reporter.report(AnnotationWarning(s"Invalid quantifier weight annotation: ${s}"))
                  None
              }
            case _ => None
          }
        }

        val body = eQuant.exp
        // Remove whitespace in identifiers to avoid parsing problems for the axiom profiler.
        // TODO: add flag to enable old behavior for AxiomProfiler
        val fallbackName = "l" + viper.silicon.utils.ast.sourceLine(sourceQuant).replaceAll(" ", "")
        val posString = if (!sourceQuant.pos.isInstanceOf[ast.AbstractSourcePosition]) {
          fallbackName
        } else {
          val pos = sourceQuant.pos.asInstanceOf[ast.AbstractSourcePosition]
          if (pos.end.isEmpty) {
            fallbackName
          } else {
            val file = pos.file.toString()
            val end = pos.end.get
            s"$file@${pos.start.line}@${pos.start.column}@${end.line}@${end.column}"
          }
        }
        val name = s"prog.$posString"
        evalQuantified(s, qantOp, eQuant.variables, Nil, Seq(body), Some(eTriggers), name, pve, v){
          case (s1, tVars, eVars, _, _, Some((Seq(tBody), bodyNew, tTriggers, (tAuxGlobal, tAux), auxExps)), v1) =>
            val tAuxHeapIndep = tAux.flatMap(v.quantifierSupporter.makeTriggersHeapIndependent(_, v1.decider.fresh))
            val auxGlobalsExp = auxExps.map(_._1)
            val auxNonGlobalsExp = auxExps.map(_._2)
            val commentGlobal = "Nested auxiliary terms: globals (aux)"
            v1.decider.prover.comment(commentGlobal)
            v1.decider.assume(tAuxGlobal, Option.when(withExp)(DebugExp.createInstance(description=commentGlobal, children=auxGlobalsExp.get)), enforceAssumption = false)
            val commentNonGlobals = "Nested auxiliary terms: non-globals (aux)"
            v1.decider.prover.comment(commentNonGlobals)
            v1.decider.assume(tAuxHeapIndep/*tAux*/, Option.when(withExp)(DebugExp.createInstance(description=commentNonGlobals, children=auxNonGlobalsExp.get)), enforceAssumption = false)

            if (qantOp == Exists) {
              // For universal quantification, the non-global auxiliary assumptions will contain the information that
              // forall vars :: all function preconditions are fulfilled.
              // However, if this quantifier is existential, they will only assume that there exist values s.t.
              // all function preconditions hold. This is not enough: We need to know (and have checked that)
              // function preconditions hold for *all* possible values of the quantified variables.
              // So we explicitly add this assumption here.
              val debugExp = Option.when(withExp)({
                val expNew = ast.Forall(eQuant.variables, eTriggers, bodyNew.get.head)(sourceQuant.pos, sourceQuant.info, sourceQuant.errT)
                val exp = ast.Forall(eQuant.variables, eTriggers, body)(sourceQuant.pos, sourceQuant.info, sourceQuant.errT)
                DebugExp.createInstance(exp, expNew)
              })
              v1.decider.assume(Quantification(Forall, tVars, FunctionPreconditionTransformer.transform(tBody, s1.program), tTriggers, name, quantWeight), debugExp)
            }

            val tQuant = Quantification(qantOp, tVars, tBody, tTriggers, name, quantWeight)
            val eQuantNew = Option.when(withExp)(buildQuantExp(qantOp, eVars.get, bodyNew.get.head, Seq.empty))
            Q(s1, tQuant, eQuantNew, v1)
          case (s1, _, _, _, _, None, v1) =>
            // This should not happen unless the current path is dead.
            if (v1.decider.checkSmoke(true)) {
              Unreachable()
            } else {
              createFailure(pve.dueTo(InternalReason(sourceQuant, "Quantifier evaluation failed.")), v1, s1, "quantifier could be evaluated")
            }
        }

      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val func = s.program.findFunction(funcName)
        evals2(s, eArgs, Nil, _ => pve, v)((s1, tArgs, eArgsNew, v1) => {
//          bookkeeper.functionApplications += 1
          val joinFunctionArgs = tArgs //++ c2a.quantifiedVariables.filterNot(tArgs.contains)
          val (debugHeapName, debugLabel) = v1.getDebugOldLabel(s1, fapp.pos)
          val s1a = if (Verifier.config.enableDebugging()) s1.copy(oldHeaps = s1.oldHeaps + (debugHeapName -> s1.h)) else s1
          /* TODO: Does it matter that the above filterNot does not filter out quantified
           *       variables that are not "raw" function arguments, but instead are used
           *       in an expression that is used as a function argument?
           *       E.g., in
           *         forall i: Int :: fun(i*i)
           *       the above filterNot will not remove i from the list of already
           *       used quantified variables because i does not match i*i.
           *       Hence, the joinedFApp will take two arguments, namely, i*i and i,
           *       although the latter is not necessary.
           */
          joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s1a, v1)((s2, v2, QB) => {
            val pres = func.pres.map(_.transform {
              /* [Malte 2018-08-20] Two examples of the test suite, one of which is the regression
               * for Carbon issue #210, fail if the subsequent code that strips out triggers from
               * exhaled function preconditions, is commented. The code was originally a work-around
               * for Silicon issue #276. Removing triggers from function preconditions is OK-ish
               * because they are consumed (exhaled), i.e. asserted. However, the triggers are
               * also used to internally generated quantifiers, e.g. related to QPs. My hope is that
               * this hack is no longer needed once heap-dependent triggers are supported.
               */
              case q: ast.Forall => q.copy(triggers = Nil)(q.pos, q.info, q.errT)
            })
            /* Formal function arguments are instantiated with the corresponding actual arguments
             * by adding the corresponding bindings to the store. To avoid formals in error messages
             * and to report actuals instead, we have two choices: the first is two attach a reason
             * transformer to the partial verification error, as done below; the second is to attach
             * a node transformer to every formal, as illustrated by NodeBacktranslationTests.scala.
             * The first approach is slightly simpler and suffices here, though.
             */
            val fargs = func.formalArgs.map(_.localVar)
            val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs).to(Map)
            val exampleTrafo = CounterexampleTransformer({
              case ce: SiliconCounterexample => ce.withStore(s2.g)
              case ce => ce
            })
            val pvePre =
              ErrorWrapperWithExampleTransformer(PreconditionInAppFalse(fapp).withReasonNodeTransformed(reasonOffendingNode =>
                reasonOffendingNode.replace(formalsToActuals)), exampleTrafo)
            val argsPairs: Seq[(Term, Option[ast.Exp])] = if (withExp) tArgs.zip(eArgsNew.get.map(Some(_))) else tArgs.zip(Seq.fill(tArgs.size)(None))
            val s3 = s2.copy(g = Store(fargs.zip(argsPairs)),
                             recordVisited = true,
                             functionRecorder = s2.functionRecorder.changeDepthBy(+1),
                                /* Temporarily disable the recorder: when recording (to later on
                                 * translate a particular function fun) and a function application
                                 * fapp is hit, then there is no need to record any information
                                 * about assertions from fapp's precondition since the latter is not
                                 * translated as part of the translation of fun.
                                 * Recording such information is even potentially harmful if formals
                                 * are not syntactically replaced by actuals but rather bound to
                                 * them via the store. Consider the following function:
                                 *   function fun(x: Ref)
                                 *     requires foo(x) // foo is another function
                                 *     ...
                                 *   { ... fun(x.next) ...}
                                 * For fun(x)'s precondition, a mapping from foo(x) to a snapshot is
                                 * recorded. When fun(x.next) is hit, its precondition is consumed,
                                 * but without substituting actuals for formals, continuing to
                                 * record mappings would add another mapping from foo(x) (which is
                                 * actually foo(x.next)) to some potentially different snapshot.
                                 * When translating fun(x) to an axiom, the snapshot of foo(x) from
                                 * fun(x)'s precondition will be the branch-condition-dependent join
                                 * of the recorded snapshots - which is wrong (probably only
                                 * incomplete).
                                 */
                             smDomainNeeded = true,
                             moreJoins = JoinMode.Off,
                             assertReadAccessOnly = if (Verifier.config.respectFunctionPrePermAmounts())
                               s2.assertReadAccessOnly /* should currently always be false */ else true)
            consumes(s3, pres, true, _ => pvePre, v2)((s4, snap, v3) => {
              val snap1 = snap.get.convert(sorts.Snap)
              val preFApp = App(functionSupporter.preconditionVersion(v3.symbolConverter.toFunction(func)), snap1 :: tArgs)
              val preExp = Option.when(withExp)({
                DebugExp.createInstance(Some(s"precondition of ${func.name}(${eArgsNew.get.mkString(", ")}) holds"), None, None, InsertionOrderedSet.empty)
              })
              v3.decider.assume(preFApp, preExp)
              val funcAnn = func.info.getUniqueInfo[AnnotationInfo]
              val tFApp = funcAnn match {
                case Some(a) if a.values.contains("opaque") =>
                  val funcAppAnn = fapp.info.getUniqueInfo[AnnotationInfo]
                  funcAppAnn match {
                    case Some(a) if a.values.contains("reveal") => App(v3.symbolConverter.toFunction(func), snap1 :: tArgs)
                    case _ => App(functionSupporter.limitedVersion(v3.symbolConverter.toFunction(func)), snap1 :: tArgs)
                  }
                case _ => App(v3.symbolConverter.toFunction(func), snap1 :: tArgs)
              }
              val fr5 =
                s4.functionRecorder.changeDepthBy(-1)
                                   .recordSnapshot(fapp, v3.decider.pcs.branchConditions, snap1)
              val s5 = s4.copy(g = s2.g,
                               h = s2.h,
                               recordVisited = s2.recordVisited,
                               functionRecorder = fr5,
                               smDomainNeeded = s2.smDomainNeeded,
                               moreJoins = s2.moreJoins,
                               assertReadAccessOnly = s2.assertReadAccessOnly)
              val funcAppNew = eArgsNew.map(args => ast.FuncApp(funcName, args)(fapp.pos, fapp.info, fapp.typ, fapp.errT))
              val funcAppNewOld = Option.when(withExp)({
                if (s5.isEvalInOld || pres.forall(_.isPure)) funcAppNew.get
                else ast.DebugLabelledOld(funcAppNew.get, debugLabel)(fapp.pos, fapp.info, fapp.errT)
              })
              QB(s5, (tFApp, funcAppNewOld), v3)})
            /* TODO: The join-function is heap-independent, and it is not obvious how a
             *       joined snapshot could be defined and represented
             */
            })(join(func.typ, s"joined_${func.name}", joinFunctionArgs, Option.when(withExp)(eArgs), v1))((s6, r, v4)
              => Q(s6, r._1, r._2, v4))})

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = s.program.findPredicate(predicateName)
        if (s.cycles(predicate) < Verifier.config.recursivePredicateUnfoldings()) {
          v.decider.startDebugSubExp()
          evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
            eval(s1, ePerm.getOrElse(ast.FullPerm()()), pve, v1)((s2, tPerm, ePermNew, v2) =>
              v2.decider.assert(IsPositive(tPerm)) { // TODO: Replace with permissionSupporter.assertNotNegative
                case true =>
                  joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s2, v2)((s3, v3, QB) => {
                    val s4 = s3.incCycleCounter(predicate)
                               .copy(recordVisited = true)
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                      predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                        val c4 = c3.decCycleCounter(predicate)
//                        eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                          QB(tIn, c5))})
                    consume(s4, acc, true, pve, v3)((s5, snap, v4) => {
                      val fr6 =
                        s5.functionRecorder.recordSnapshot(pa, v4.decider.pcs.branchConditions, snap.get)
                                           .changeDepthBy(+1)
                      val s6 = s5.copy(functionRecorder = fr6,
                                       constrainableARPs = s1.constrainableARPs)

                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      if (!Verifier.config.disableFunctionUnfoldTrigger()) {
                        val eArgsString = eArgsNew.mkString(", ")
                        val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($eArgsString))", isInternal_ = true))
                        v4.decider.assume(App(s.predicateData(predicate).triggerFunction, snap.get.convert(terms.sorts.Snap) +: tArgs), debugExp)
                      }
                      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
                      val s7 = s6.scalePermissionFactor(tPerm, ePermNew)
                      val argsPairs: List[(Term, Option[ast.Exp])] = if (withExp) tArgs zip eArgsNew.get.map(Some(_)) else tArgs zip Seq.fill(tArgs.size)(None)
                      val insg = s7.g + Store(predicate.formalArgs map (_.localVar) zip argsPairs)
                      val s7a = s7.copy(g = insg).setConstrainable(s7.constrainableARPs, false)
                      produce(s7a, toSf(snap.get), body, pve, v4)((s8, v5) => {
                        val s9 = s8.copy(g = s7.g,
                                         functionRecorder = s8.functionRecorder.changeDepthBy(-1),
                                         recordVisited = s3.recordVisited,
                                         permissionScalingFactor = s6.permissionScalingFactor,
                                         permissionScalingFactorExp = s6.permissionScalingFactorExp,
                                         constrainableARPs = s1.constrainableARPs)
                                   .decCycleCounter(predicate)
                        val s10 = v5.stateConsolidator(s9).consolidateOptionally(s9, v5)
                        eval(s10, eIn, pve, v5)((s9, t9, e9, v9) => QB(s9, (t9, e9), v9))})})
                  })(join(eIn.typ, "joined_unfolding", s2.relevantQuantifiedVariables.map(_._1),
                    Option.when(withExp)(s2.relevantQuantifiedVariables.map(_._2.get)), v2))((s12, r12, v7)
                    => {
                    v7.decider.finishDebugSubExp(s"unfolded(${predicate.name})")
                    Q(s12, r12._1, r12._2, v7)})
                case false =>
                  v2.decider.finishDebugSubExp(s"unfolded(${predicate.name})")
                  createFailure(pve dueTo NonPositivePermission(ePerm.get), v2, s2, IsPositive(tPerm), ePermNew.map(p => ast.PermGtCmp(p, ast.NoPerm()())(p.pos, p.info, p.errT)))}))
        } else {
          val unknownValue = v.decider.appliedFresh("recunf", v.symbolConverter.toSort(eIn.typ), s.relevantQuantifiedVariables.map(_._1))
          Q(s, unknownValue, Option.when(withExp)(ast.LocalVarWithVersion("unknownValue", eIn.typ)(eIn.pos, eIn.info, eIn.errT)), v)
        }

      case ast.Applying(wand, eIn) =>
        joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s, v)((s1, v1, QB) =>
          magicWandSupporter.applyWand(s1, wand, pve, v1)((s2, v2) => {
            eval(s2, eIn, pve, v2)((s3, t, eInNew, v3) => QB(s3, (t, eInNew), v3))
        }))(join(eIn.typ, "joined_applying", s.relevantQuantifiedVariables.map(_._1),
          Option.when(withExp)(s.relevantQuantifiedVariables.map(_._2.get)), v))((s4, r4, v4)
          => Q(s4, r4._1, r4._2, v4))

      case ast.Asserting(eAss, eIn) =>
        consume(s, eAss, false, pve, v)((s2, _, v2) => {
          val s3 = s2.copy(g = s.g, h = s.h)
          eval(s3, eIn, pve, v2)(Q)
        })

      /* Sequences */

      case ast.SeqContains(e0, e1) => evalBinOp(s, e1, e0, SeqIn, pve, v)((s1, t, e1New, e0New, v1) =>
        Q(s1, t, e0New.map(e0p => ast.SeqContains(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        /* Note the reversed order of the arguments! */

      case ast.SeqIndex(e0, e1) =>
        evals2(s, Seq(e0, e1), Nil, _ => pve, v)({case (s1, Seq(t0, t1), esNew, v1) =>
          val eNew = esNew.map(es => ast.SeqIndex(es.head, es(1))(e.pos, e.info, e.errT))
          if (s1.triggerExp) {
            Q(s1, SeqAt(t0, t1), eNew, v1)
          } else {
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqAt(t0, t1), eNew, v1)
                  case false =>
                    val assertExp2 = Option.when(withExp)(ast.LtCmp(e1, ast.SeqLength(e0)())(e1.pos, e1.info, e1.errT))
                    val failure = createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1, Less(t1, SeqLength(t0)), assertExp2)
                    if (s1.retryLevel == 0 && v1.reportFurtherErrors()) {
                      val assertExp2 = Option.when(withExp)(ast.LeCmp(e1, ast.SeqLength(e0)())())
                      val assertExp2New = esNew.map(es => ast.LeCmp(es(1), ast.SeqLength(es.head)())())
                      v1.decider.assume(Less(t1, SeqLength(t0)), assertExp2, assertExp2New)
                      failure combine Q(s1, SeqAt(t0, t1), eNew, v1)
                    } else failure}
              case false =>
                val assertExp1 = Option.when(withExp)(ast.GeCmp(e1, ast.IntLit(0)())(e1.pos, e1.info, e1.errT))
                val assertExp1New = Option.when(withExp)(ast.GeCmp(esNew.get(1), ast.IntLit(0)())(e1.pos, e1.info, e1.errT))
                val failure1 = createFailure(pve dueTo SeqIndexNegative(e0, e1), v1, s1, AtLeast(t1, IntLiteral(0)), assertExp1New)
                if (s1.retryLevel == 0 && v1.reportFurtherErrors()) {
                  v1.decider.assume(AtLeast(t1, IntLiteral(0)), assertExp1, assertExp1New)
                  val assertExp2 = Option.when(withExp)(ast.LtCmp(e1, ast.SeqLength(e0)())(e1.pos, e1.info, e1.errT))
                  val assertExp2New = Option.when(withExp)(ast.LtCmp(esNew.get(1), ast.SeqLength(esNew.get(0))())(e1.pos, e1.info, e1.errT))
                  v1.decider.assert(Less(t1, SeqLength(t0))) {
                    case true =>
                      failure1 combine Q(s1, SeqAt(t0, t1), eNew, v1)
                    case false =>
                      val failure2 = failure1 combine createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1, Less(t1, SeqLength(t0)), assertExp2New)
                      if (v1.reportFurtherErrors()) {
                        v1.decider.assume(Less(t1, SeqLength(t0)), assertExp2, assertExp2New)
                        failure2 combine Q(s1, SeqAt(t0, t1), eNew, v1)
                      } else failure2}
                } else failure1}}})

      case ast.SeqAppend(e0, e1) => evalBinOp(s, e0, e1, SeqAppend, pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, e0New.map(e0p => ast.SeqAppend(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
      case ast.SeqDrop(e0, e1) => evalBinOp(s, e0, e1, SeqDrop, pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, e0New.map(e0p => ast.SeqDrop(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
      case ast.SeqTake(e0, e1) => evalBinOp(s, e0, e1, SeqTake, pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, e0New.map(e0p => ast.SeqTake(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
      case ast.SeqLength(e0) => eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
        Q(s1, SeqLength(t0), e0New.map(e0p => ast.SeqLength(e0p)(e.pos, e.info, e.errT)), v1))
      case ast.EmptySeq(typ) => Q(s, SeqNil(v.symbolConverter.toSort(typ)), Option.when(withExp)(e), v)
      case ast.RangeSeq(e0, e1) => evalBinOp(s, e0, e1, SeqRanged, pve, v)((s1, t, e0New, e1New, v1) =>
        Q(s1, t, e0New.map(e0p => ast.RangeSeq(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))

      case ast.SeqUpdate(e0, e1, e2) =>
        evals2(s, Seq(e0, e1, e2), Nil, _ => pve, v)({ case (s1, Seq(t0, t1, t2), esNew, v1) =>
          val eNew = esNew.map(es => ast.SeqUpdate(es.head, es(1), es(2))(e.pos, e.info, e.errT))
          if (s1.triggerExp) {
            Q(s1, SeqUpdate(t0, t1, t2), eNew, v1)
          } else {
            val assertExp = Option.when(withExp)(ast.GeCmp(e1, ast.IntLit(0)())(e1.pos, e1.info, e1.errT))
            val assertExpNew = Option.when(withExp)(ast.GeCmp(esNew.get(1), ast.IntLit(0)())(e1.pos, e1.info, e1.errT))
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                val assertExp2New = Option.when(withExp)(ast.LtCmp(esNew.get(1), ast.SeqLength(esNew.get(0))())(e1.pos, e1.info, e1.errT))
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqUpdate(t0, t1, t2), eNew, v1)
                  case false =>
                    val failure = createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1, Less(t1, SeqLength(t0)), assertExp2New)
                    if (s1.retryLevel == 0 && v1.reportFurtherErrors()) {
                      val assertExp3 = Option.when(withExp)(ast.LeCmp(e1, ast.SeqLength(e0)())())
                      val assertExp3New = Option.when(withExp)(ast.LeCmp(esNew.get(1), ast.SeqLength(esNew.get(0))())())
                      v1.decider.assume(Less(t1, SeqLength(t0)), assertExp3, assertExp3New)
                      failure combine Q(s1, SeqUpdate(t0, t1, t2), eNew, v1)}
                    else failure}
              case false =>
                val failure1 = createFailure(pve dueTo SeqIndexNegative(e0, e1), v1, s1, AtLeast(t1, IntLiteral(0)), assertExpNew)
                if (s1.retryLevel == 0 && v1.reportFurtherErrors()) {
                  v1.decider.assume(AtLeast(t1, IntLiteral(0)), assertExp, assertExpNew)
                  val assertExp2 = Option.when(withExp)(ast.LtCmp(e1, ast.SeqLength(e0)())(e1.pos, e1.info, e1.errT))
                  val assertExp2New = Option.when(withExp)(ast.LtCmp(esNew.get(1), ast.SeqLength(esNew.get(0))())(e1.pos, e1.info, e1.errT))
                  v1.decider.assert(Less(t1, SeqLength(t0))) {
                    case true =>
                      failure1 combine Q(s1, SeqUpdate(t0, t1, t2), eNew, v1)
                    case false =>
                      val failure2 = failure1 combine createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1, Less(t1, SeqLength(t0)), assertExp2New)
                      if (v1.reportFurtherErrors()) {
                        v1.decider.assume(Less(t1, SeqLength(t0)), assertExp2, assertExp2New)
                        failure2 combine Q(s1, SeqUpdate(t0, t1, t2), eNew, v1)
                      } else failure2}
            } else failure1}}})

      case seq@ast.ExplicitSeq(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, esNew, v1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(tSeq, SeqSingleton(te)))
          val debugExp = Option.when(withExp)({
            val expNew = ast.EqCmp(ast.SeqLength(ast.ExplicitSeq(esNew.get)())(), ast.IntLit(es.size)())(seq.pos, seq.info, seq.errT)
            val exp = ast.EqCmp(ast.SeqLength(seq)(), ast.IntLit(es.size)())(seq.pos, seq.info, seq.errT)
            DebugExp.createInstance(exp, expNew)
          })
          v1.decider.assume(SeqLength(tSeq) === IntLiteral(es.size), debugExp)
          Q(s1, tSeq, esNew.map(en => ast.ExplicitSeq(en)(e.pos, e.info, e.errT)), v1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) =>
        Q(s, EmptySet(v.symbolConverter.toSort(typ)), Option.when(withExp)(e), v)
      case ast.EmptyMultiset(typ) =>
        Q(s, EmptyMultiset(v.symbolConverter.toSort(typ)), Option.when(withExp)(e), v)

      case ast.ExplicitSet(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, esNew, v1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(s1, tSet, esNew.map(es => ast.ExplicitSet(es)(e.pos, e.info, e.errT)), v1)})

      case ast.ExplicitMultiset(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, esNew, v1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(s1, tMultiset, esNew.map(es => ast.ExplicitMultiset(es)(e.pos, e.info, e.errT)), v1)})

      case ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetUnion, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetUnion(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetUnion, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetUnion(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIntersection, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetIntersection(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetIntersection, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetIntersection(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetSubset, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetSubset(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetSubset, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetSubset(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetDifference, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetMinus(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetDifference, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetMinus(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIn, pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetContains(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => evalBinOp(s, e0, e1, (t0, t1) => MultisetCount(t1, t0), pve, v)((s1, t, e0New, e1New, v1)
          => Q(s1, t, e0New.map(e0p => ast.AnySetContains(e0p, e1New.get)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.SetType => eval(s, e0, pve, v)((s1, t0, e0New, v1)
          => Q(s1, SetCardinality(t0), e0New.map(e0p => ast.AnySetCardinality(e0p)(e.pos, e.info, e.errT)), v1))
        case _: ast.MultisetType => eval(s, e0, pve, v)((s1, t0, e0New, v1)
          => Q(s1, MultisetCardinality(t0), e0New.map(e0p => ast.AnySetCardinality(e0p)(e.pos, e.info, e.errT)), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }

      /* Maps */

      case ast.EmptyMap(keyType, valueType) =>
        Q(s, EmptyMap(v.symbolConverter.toSort(keyType), v.symbolConverter.toSort(valueType)), Option.when(withExp)(e), v)
      case em: ast.ExplicitMap =>
        eval(s, em.desugared, pve, v)((s1, t0, _, v1) => Q(s1, t0, Option.when(withExp)(em), v1))
      case ast.MapCardinality(base) =>
        eval(s, base, pve, v)((s1, t0, baseNew, v1) => Q(s1, MapCardinality(t0), baseNew.map(ast.MapCardinality(_)(e.pos, e.info, e.errT)), v1))
      case ast.MapDomain(base) =>
        eval(s, base, pve, v)((s1, t0, baseNew, v1) => Q(s1, MapDomain(t0), baseNew.map(ast.MapDomain(_)(e.pos, e.info, e.errT)), v1))
      case ast.MapRange(base) =>
        eval(s, base, pve, v)((s1, t0, baseNew, v1) => Q(s1, MapRange(t0), baseNew.map(ast.MapRange(_)(e.pos, e.info, e.errT)), v1))

      case ml@ast.MapLookup(base, key) =>
        evals2(s, Seq(base, key), Nil, _ => pve, v)({
          case (s1, Seq(baseT, keyT), esNew, v1) if s1.triggerExp =>
            Q(s1, MapLookup(baseT, keyT), esNew.map(es => ast.MapLookup(es(0), es(1))(e.pos, e.info, e.errT)), v1)
          case (s1, Seq(baseT, keyT), esNew, v1) =>
            val eNew = esNew.map(es => ast.MapLookup(es(0), es(1))(e.pos, e.info, e.errT))
            v1.decider.assert(SetIn(keyT, MapDomain(baseT))) {
              case true => Q(s1, MapLookup(baseT, keyT), eNew, v1)
              case false =>
                val assertExp = Option.when(withExp)(ast.MapContains(key, base)(ml.pos, ml.info, ml.errT))
                val assertExpNew = Option.when(withExp)(ast.MapContains(esNew.get(1), esNew.get(0))(ml.pos, ml.info, ml.errT))
                val failure1 = createFailure(pve dueTo MapKeyNotContained(base, key), v1, s1, SetIn(keyT, MapDomain(baseT)), assertExpNew)
                if (s1.retryLevel == 0 && v1.reportFurtherErrors()) {
                  v1.decider.assume(SetIn(keyT, MapDomain(baseT)), assertExp, assertExpNew)
                  failure1 combine Q(s1, MapLookup(baseT, keyT), eNew, v1)
                } else {
                  failure1
                }
            }
        })

      case ast.MapUpdate(base, key, value) =>
        evals2(s, Seq(base, key, value), Nil, _ => pve, v)({
          case (s1, Seq(baseT, keyT, valueT), esNew, v1)
            => Q(s1, MapUpdate(baseT, keyT, valueT), esNew.map(es => ast.MapUpdate(es(0), es(1), es(2))(e.pos, e.info, e.errT)), v1)
        })

      case ast.MapContains(key, base) =>
        evals2(s, Seq(key, base), Nil, _ => pve, v)({
          case (s1, Seq(keyT, baseT), esNew, v1) => Q(s1, SetIn(keyT, MapDomain(baseT)), esNew.map(es => ast.MapContains(es(0), es(1))(e.pos, e.info, e.errT)), v1)
        })

      /* Unexpected nodes */

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(e), v, s, "valid AST")

      case _: ast.EpsilonPerm
         | _: ast.Maplet
         | _: ast.FieldAccessPredicate
         | _: ast.MagicWand
         | _: ast.PredicateAccess
         | _: ast.PredicateAccessPredicate
         | _: ast.ExtensionExp =>
        sys.error(s"Unexpected expression $e cannot be symbolically evaluated")
    }

    resultTerm
  }

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp], /* Are evaluated and added as path conditions before ...*/
                     es2: Seq[ast.Exp], /* ... these terms are evaluated */
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State,
                         Seq[Var], /* Variables from vars */
                         Option[Seq[ast.LocalVarDecl]],
                         Seq[Term], /* Terms from es1 */
                         Option[Seq[ast.Exp]],
                         Option[( /* None if es2 or trigger evaluation did not result in a term because es1 is unsatisfiable */
                            Seq[Term], /* Terms from es2 */
                            Option[Seq[ast.Exp]],
                            Seq[Trigger], /* Triggers from optTriggers */
                            (Seq[Term], Seq[Quantification]), /* Global and non-global auxiliary assumptions */
                            Option[(InsertionOrderedSet[DebugExp], InsertionOrderedSet[DebugExp])]
                         )],
                         Verifier) => VerificationResult)
                    : VerificationResult = {

    val localVars = vars map (_.localVar)

    val varPairs: Seq[(Var, Option[ast.LocalVarWithVersion])] = localVars map v.decider.fresh
    val tVars: Seq[Var] = varPairs map (_._1)
    val gVars = Store(localVars zip varPairs)
    val s1 = s.copy(g = s.g + gVars,
                    quantifiedVariables = varPairs ++ s.quantifiedVariables,
                    recordPossibleTriggers = true,
                    possibleTriggers = Map.empty) // TODO: Why reset possibleTriggers if they are merged with s.possibleTriggers later anyway?
    type R = (State, Seq[Term], Option[Seq[ast.Exp]], Option[(Seq[Term], Option[Seq[ast.Exp]], Seq[Trigger], (Seq[Term], Seq[Quantification]), Option[(InsertionOrderedSet[DebugExp], InsertionOrderedSet[DebugExp])], Map[ast.Exp, Term])])
    executionFlowController.locallyWithResult[R](s1, v)((s2, v1, QB) => {
       val preMark = v1.decider.setPathConditionMark()
      evals(s2, es1, _ => pve, v1)((s3, ts1, es1New, v2) => {
        val bc = And(ts1)
        // ME: If bc is unsatisfiable, we are assuming false here. In that case, evaluating es2 and the triggers
        // may not return any value (e.g. if es2 contains a field read for which we don't have permission, a smoke
        // check succeeds, then the continuation for evals(es2) is never invoked). This caused issue #842.
        // In this case, we return None.
        val expPair = (viper.silicon.utils.ast.BigAnd(es1), es1New.map(viper.silicon.utils.ast.BigAnd(_)))
        v2.decider.setCurrentBranchCondition(bc, expPair)
        var es2AndTriggerTerms: Option[(Seq[Term], Option[Seq[ast.Exp]], Seq[Trigger], (Seq[Term], Seq[Quantification]), Option[(InsertionOrderedSet[DebugExp], InsertionOrderedSet[DebugExp])], Map[ast.Exp, Term])] = None
        var finalState = s3
        val es2AndTriggerResult = evals(s3, es2, _ => pve, v2)((s4, ts2, es2New, v3) => {
          evalTriggers(s4, optTriggers.getOrElse(Nil), pve, v3)((s5, tTriggers, _) => { // TODO: v4 isn't forward - problem?
            val (auxGlobals, auxNonGlobalQuants) =
              v3.decider.pcs.after(preMark).quantified(quant, tVars, tTriggers, s"$name-aux", isGlobal = false, bc)
            val auxExps =
              Option.when(withExp)(v3.decider.pcs.after(preMark).quantifiedExp(quant, varPairs map (_._2.get), tVars, optTriggers.getOrElse(Nil), tTriggers, s"$name-aux", isGlobal = false, bc))
            val additionalPossibleTriggers: Map[ast.Exp, Term] =
              if (s.recordPossibleTriggers) s5.possibleTriggers else Map()
            es2AndTriggerTerms = Some((ts2, es2New, tTriggers, (auxGlobals, auxNonGlobalQuants), auxExps, additionalPossibleTriggers))
            finalState = s5
            Success()
          })})
        es2AndTriggerResult combine QB((finalState, ts1, es1New, es2AndTriggerTerms))
      })
    }){
      case (s2, ts1, es1New1, Some((ts2, es2New1, tTriggers, (tAuxGlobal, tAux), eAuxExps, additionalPossibleTriggers))) =>
        val s3 = s.copy(possibleTriggers = s.possibleTriggers ++ additionalPossibleTriggers)
                .preserveAfterLocalEvaluation(s2)
        Q(s3, tVars, Option.when(withExp)(varPairs map (e => ast.LocalVarDecl(e._2.get.name, e._2.get.typ)(e._2.get.pos, e._2.get.info, e._2.get.errT))), ts1, es1New1, Some((ts2, es2New1, tTriggers, (tAuxGlobal, tAux), Option.when(withExp)((eAuxExps.get._1, eAuxExps.get._2)))), v)
      case (s2, ts1, es1New1, None) =>
        Q(s2, tVars, Option.when(withExp)(varPairs map (e => ast.LocalVarDecl(e._2.get.name, e._2.get.typ)(e._2.get.pos, e._2.get.info, e._2.get.errT))), ts1, es1New1, None, v)
    }
  }

  private def evalImplies(s: State,
                          tLhs: Term,
                          eLhs: (ast.Exp, Option[ast.Exp]),
                          eRhs: ast.Exp,
                          fromShortCircuitingAnd: Boolean,
                          pve: PartialVerificationError,
                          v: Verifier)
                         (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
                         : VerificationResult = {

    joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s, v)((s1, v1, QB) =>
      brancher.branch(s1.copy(parallelizeBranches = false), tLhs, eLhs, v1, fromShortCircuitingAnd = fromShortCircuitingAnd)(
        (s2, v2) => eval(s2.copy(parallelizeBranches = s1.parallelizeBranches), eRhs, pve, v2)((s2, tRhs, eRhsNew, v2) => QB(s2, (tRhs, eRhsNew), v2)),
        (s2, v2) => QB(s2.copy(parallelizeBranches = s1.parallelizeBranches), (True, Option.when(withExp)(ast.TrueLit()())), v2))
    )(entries => {
      assert(entries.length <= 2)
      val s1 = entries.tail.foldLeft(entries.head.s)((sAcc, entry) => sAcc.merge(entry.s))
      val t = Implies(tLhs, entries.headOption.map(_.data._1).getOrElse(True))
      val e = eLhs._2.map(lhs => ast.Implies(lhs, entries.headOption.map(_.data._2.get).getOrElse(ast.TrueLit()()))())
      (s1, (t, e))
    })((s3, r3, v3) => {
      val (t3, e3) = r3
      Q(s3, t3, e3, v3)
    })
  }

  private def evalInOldState(s: State,
                             label: String,
                             e: ast.Exp,
                             pve: PartialVerificationError,
                             v: Verifier)
                            (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
                            : VerificationResult = {

    val h = s.oldHeaps(label)
    val s1 = s.copy(h = h, partiallyConsumedHeap = None, isEvalInOld = true)
    val s2 = v.stateConsolidator(s1).consolidateOptionally(s1, v)
    val possibleTriggersBefore: Map[ast.Exp, Term] = if (s.recordPossibleTriggers) s.possibleTriggers else Map.empty

    eval(s2, e, pve, v)((s3, t, eNew, v1) => {
      val newPossibleTriggers = if (s.recordPossibleTriggers) {
        // For all new possible trigger expressions e and translated term t,
        // make sure we remember t as the term for old[label](e) instead.
        // If e is not heap-dependent, we also remember t as the term for e.
        val addedOrChangedPairs = s3.possibleTriggers.filter(t =>
          !possibleTriggersBefore.contains(t._1) || possibleTriggersBefore(t._1) != t._2)

        def wrapInOld(e: ast.Exp) = {
          if (label == Verifier.PRE_STATE_LABEL) {
            ast.Old(e)(e.pos, e.info, e.errT)
          } else {
            ast.LabelledOld(e, label)(e.pos, e.info, e.errT)
          }
        }

        val oldPairs = addedOrChangedPairs.map(t => wrapInOld(t._1) -> t._2) ++
          addedOrChangedPairs.filter(t => !t._1.isHeapDependent(s.program))
        s.possibleTriggers ++ oldPairs
      } else {
        s.possibleTriggers
      }
      val s4 = s3.copy(h = s.h,
                       oldHeaps = s3.oldHeaps + (label -> s3.h),
                       partiallyConsumedHeap = s.partiallyConsumedHeap,
                       possibleTriggers = newPossibleTriggers,
                       isEvalInOld = false)
      Q(s4, t, eNew, v1)})
  }

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                        : VerificationResult = {

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvr1, v1) =>
          Q(s1, field.name, tRcvr :: Nil, eRcvr1.map(_ :: Nil), v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgs1, v1) =>
          Q(s1, predicateName, tArgs, eArgs1, v1))
    }
  }

  def evalResourceAccess(s: State, resacc: ast.ResourceAccess, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, ChunkIdentifer, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                        : VerificationResult = {
    resacc match {
      case wand : ast.MagicWand =>
        magicWandSupporter.evaluateWandArguments(s, wand, pve, v)((s1, tArgs, eArgsNew, v1) =>
        Q(s1, MagicWandIdentifier(wand, s.program), tArgs, eArgsNew, v1))
      case ast.FieldAccess(eRcvr, field) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvrNew, v1) =>
          Q(s1, BasicChunkIdentifier(field.name), tRcvr :: Nil, eRcvrNew.map(_ :: Nil), v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          Q(s1, BasicChunkIdentifier(predicateName), tArgs, eArgsNew, v1))
    }
  }

  private def evalBinOp[T <: Term](s: State,
                                   e0: ast.Exp,
                                   e1: ast.Exp,
                                   termOp: ((Term, Term)) => T,
                                   pve: PartialVerificationError,
                                   v: Verifier)
                                  (Q: (State, T, Option[ast.Exp], Option[ast.Exp], Verifier) => VerificationResult)
                                  : VerificationResult = {

    evalBinOp(s, e0, e1, (t0, t1) => termOp((t0, t1)), pve, v)(Q)
  }

  private def evalBinOp[T <: Term]
                       (s: State,
                        e0: ast.Exp,
                        e1: ast.Exp,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
                        v: Verifier)
                       (Q: (State, T, Option[ast.Exp], Option[ast.Exp], Verifier) => VerificationResult)
                       : VerificationResult = {

    eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
      eval(s1, e1, pve, v1)((s2, t1, e1New, v2) =>
        Q(s2, termOp(t0, t1), e0New, e1New, v2)))
  }

  private def failIfDivByZero(s: State,
                              t: Term,
                              eDivisor: ast.Exp,
                              eDivisorNew: Option[ast.Exp],
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              v: Verifier)
                             (Q: (State, Term, Verifier) => VerificationResult)
                             : VerificationResult = {

    v.decider.assert(tDivisor !== tZero){
      case true => Q(s, t, v)
      case false =>
        val (notZeroExp, notZeroExpNew) = if (withExp) {
          (Some(ast.NeCmp(eDivisor, ast.IntLit(0)())(eDivisor.pos, eDivisor.info, eDivisor.errT)), Some(ast.NeCmp(eDivisorNew.get, ast.IntLit(0)())(eDivisor.pos, eDivisor.info, eDivisor.errT)))
        } else { (None, None) }
        val failure = createFailure(pve dueTo DivisionByZero(eDivisor), v, s, tDivisor !== tZero, notZeroExpNew)
        if (s.retryLevel == 0  && v.reportFurtherErrors()) {
          v.decider.assume(tDivisor !== tZero, notZeroExp, notZeroExpNew)
          failure combine Q(s, t, v)
        } else failure
    }
  }

  def evalTriggers(s: State,
                   silverTriggers: Seq[ast.Trigger],
                   pve: PartialVerificationError,
                   v: Verifier)
                  (Q: (State, Seq[Trigger], Verifier) => VerificationResult)
                   : VerificationResult = {

    evalTriggers(s, silverTriggers map (_.exps), Nil, pve, v)((s1, tTriggersSets, v1) => {
      /* [2015-12-15 Malte]
       *   Evaluating triggers that did not occur in the body (and whose corresponding term has
       *   therefore not already been recorded in the context) might introduce new path conditions,
       *   in particular, new constants/functions and their definitions.
       *   This is, for example, the case in issue_0147.sil: the trigger generator can potentially
       *   replace the arithmetic expression `j+1` by a fresh, quantified variable (in the trigger,
       *   not necessarily in the quantifier body). Since it is part of the receiver of a quantified
       *   field dereference, the trigger mentioning the fresh variable might only be evaluated when
       *   evaluating the triggers, potentially leading to a newly introduced field value function.
       *
       *   TODO: Currently, new path conditions introduced while evaluating triggers will not be
       *         added to the auxiliary quantifier, i.e. they will not survive when the scope in
       *         which the quantifier (resp., its body and its triggers) is evaluated.
       *         Using such effectively "undefined" symbols in triggers will most likely result in
       *         incompletenesses because the corresponding quantifiers will not be triggered.
       */

      Q(s1, tTriggersSets map Trigger, v1)})
  }

  /** Evaluates the given list of trigger sets `eTriggerSets` (expressions) and passes the result
    * plus the initial trigger sets `tTriggerSets` (terms) to the continuation `Q`.
    */
  private def evalTriggers(s: State,
                           eTriggerSets: TriggerSets[ast.Exp],
                           tTriggersSets: TriggerSets[Term],
                           pve: PartialVerificationError,
                           v: Verifier)
                          (Q: (State, TriggerSets[Term], Verifier) => VerificationResult)
                          : VerificationResult = {

    if (eTriggerSets.isEmpty)
      Q(s, tTriggersSets, v)
    else {
      if (eTriggerSets.head.collect{case fa: ast.FieldAccess => fa; case pa: ast.PredicateAccess => pa; case wand: ast.MagicWand => wand }.nonEmpty ) {
        evalHeapTrigger(s, eTriggerSets.head, pve, v)((s1, ts, v1) =>
          evalTriggers(s1, eTriggerSets.tail, tTriggersSets :+ ts, pve, v1)(Q))
      } else {
        evalTrigger(s, eTriggerSets.head, pve, v)((s1, ts, v1) =>
          evalTriggers(s1, eTriggerSets.tail, tTriggersSets :+ ts, pve, v1)(Q))
      }}
  }

  private def evalTrigger(s: State, exps: Seq[ast.Exp], pve: PartialVerificationError, v: Verifier)
                         (Q: (State, Seq[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    def transformPotentialFuncApp(t: Term) = t match {
      case app@App(fun: HeapDepFun, _) =>
        /** Heap-dependent functions that are used as tTriggerSets should be used
          * in the limited version, because it allows for more instantiations.
          * Keep this code in sync with [[viper.silicon.supporters.ExpressionTranslator.translate]]
          *
          */
        app.copy(applicable = functionSupporter.limitedVersion(fun))
      case other =>
        other
    }

    val (cachedTriggerTerms, remainingTriggerExpressions) =
      exps.map {
        case pt @ (_: ast.PossibleTrigger | _: ast.FieldAccess | _: ast.LabelledOld | _: ast.Old) =>
          val cachedTrigger = s.possibleTriggers.get(pt).map(t => transformPotentialFuncApp(t))
          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(pt))
        case e => (None, Some(e))
      }.unzip match {
        case (optCachedTriggerTerms, optRemainingTriggerExpressions) =>
          (optCachedTriggerTerms.flatten, optRemainingTriggerExpressions.flatten)
      }

    /* Reasons for why a trigger wasn't recorded while evaluating the body include:
     *   - It did not occur in the body
     *   - The evaluation of the body terminated early, for example, because the
     *     LHS of an implication evaluated to false
     */

    var optRemainingTriggerTerms: Option[Seq[Term]] = None
    // Setting a mark pushes a scope that needs to be popped again later, see below.
    val preMark = v.decider.setPathConditionMark()
    var pcDelta = InsertionOrderedSet.empty[Term]
    var pcDeltaExp = InsertionOrderedSet.empty[DebugExp]

    /* TODO: Evaluate as many remaining expressions as possible, i.e. don't
     *       stop if evaluating one fails
     *
     *       Here is an example where evaluating remainingTriggerExpressions will
     *       fail: Assume a conjunction f(x) && g(x) where f(x) is the
     *       precondition of g(x). This gives rise to the trigger {f(x), g(x)}.
     *       If the two trigger expressions are evaluated individually, evaluating
     *       the second will fail because its precondition doesn't hold.
     *       For example, let f(x) be "x in xs" (and assume that this, via other
     *       path conditions, implies that x != null), and let g(x) be "y.f in xs".
     *       Evaluating the latter will currently fail when evaluating y.f because
     *       y on its own (i.e., without having assumed y in xs) might be null.
     *
     *       What might be possible is to merely translate (instead of evaluate)
     *       triggers, where the difference is that translating does not entail
     *       any checks such as checking for non-nullity.
     *       In case of applications of heap. dep. functions this won't be
     *       straight-forward, because the resulting FApp-term expects a snapshot,
     *       which is computed by (temporarily) consuming the function's
     *       precondition.
     *       We could replace each concrete snapshot occurring in an FApp-term by
     *       a quantified snapshot, but that might make the chosen triggers invalid
     *       because some trigger sets might no longer cover all quantified
     *       variables.
     */

    /* TODO: Use executionFlowController.locally instead of val r = ...; r && { ... }.
     *       This is currently not possible because executionFlowController.locally will only
     *       continue after the local block if the block was successful (i.e. if it yielded
     *       Success()). However, here we want to continue in any case.
     */

    val r =
      evals(s, remainingTriggerExpressions, _ => pve, v)((_, remainingTriggerTerms, _, v1) => {
        optRemainingTriggerTerms = Some(remainingTriggerTerms)
        pcDelta = v1.decider.pcs.after(preMark).assumptions //decider.π -- πPre
        pcDeltaExp = v1.decider.pcs.after(preMark).assumptionExps
        Success()})

    // Remove all assumptions resulting from evaluating the trigger.
    // IF trigger evaluation was successful, we will assume them again (see success case below).
    // However, they need to be removed for now since they would otherwise be assumed unconditionally
    // (since the preMark layer has no branch conditions), and we can assume them only conditionally.
    // See issue #688 for an example of what happens otherwise.
    v.decider.pcs.popUntilMark(preMark)

    (r, optRemainingTriggerTerms) match {
      case (Success(), Some(remainingTriggerTerms)) =>
        v.decider.assume(pcDelta, Option.when(withExp)(DebugExp.createInstance("pcDeltaExp", children = pcDeltaExp)), enforceAssumption = false)
        Q(s, cachedTriggerTerms ++ remainingTriggerTerms, v)
      case _ =>
        for (e <- remainingTriggerExpressions)
          v.reporter.report(WarningsDuringVerification(Seq(
            VerifierWarning(s"Might not be able to use trigger $e, since it is not evaluated while evaluating the body of the quantifier", e.pos))))
        Q(s, cachedTriggerTerms, v)
    }
  }

  private def join(joinType: ast.Type,
                   joinFunctionName: String,
                   joinFunctionArgs: Seq[Term],
                   joinFunctionArgsExp: Option[Seq[ast.Exp]],
                   v: Verifier)
                  (entries: Seq[JoinDataEntry[(Term, Option[ast.Exp])]])
                  : (State, (Term, Option[ast.Exp])) = {

    val joinSort = v.symbolConverter.toSort(joinType)
    assert(entries.nonEmpty, "Expected at least one join data entry")

    entries match {
      case Seq(entry) =>
        /* If there is only one entry, i.e. one branch to join, it is assumed that the other
         * branch was infeasible, and the branch conditions are therefore ignored.
         */
        (entry.s, entry.data)
      case _ =>
        val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
        val joinSymbol = v.decider.fresh(joinFunctionName, quantifiedVarsSorts, joinSort)
        val joinTerm = App(joinSymbol, joinFunctionArgs)
        val joinExp = joinFunctionArgsExp.map(jfa => ast.FuncApp(joinFunctionName, jfa)(ast.NoPosition, ast.NoInfo, joinType, ast.NoTrafos))

        val joinDefEqs: Seq[(Term, Option[ast.Exp], Option[ast.Exp])] = entries map (entry =>
          (Implies(And(entry.pathConditions.branchConditions), BuiltinEquals(joinTerm, entry.data._1)),
          Option.when(withExp)(ast.Implies(BigAnd(entry.pathConditions.branchConditionExps.map(bc => bc._1)), ast.EqCmp(joinExp.get, entry.data._2.get)())()),
          Option.when(withExp)(ast.Implies(BigAnd(entry.pathConditions.branchConditionExps.map(bc => bc._2.get)), ast.EqCmp(joinExp.get, entry.data._2.get)())())))


        var sJoined = entries.tail.foldLeft(entries.head.s)((sAcc, entry) => sAcc.merge(entry.s))
        sJoined = sJoined.copy(functionRecorder = sJoined.functionRecorder.recordPathSymbol(joinSymbol))

        joinDefEqs foreach { case (t, exp, expNew) => v.decider.assume(t, exp, expNew)}

        (sJoined, (joinTerm, joinExp))
    }
  }

  private def evalHeapTrigger(s: State, exps: Seq[ast.Exp], pve: PartialVerificationError, v: Verifier)
                             (Q: (State, Seq[Term], Verifier) => VerificationResult) : VerificationResult = {
    var triggers: Seq[Term] = Seq()
    var triggerAxioms: Seq[Term] = Seq()
    var smDefs: Seq[SnapshotMapDefinition] = Seq()

    exps foreach {
      case fa: ast.FieldAccess if s.heapDependentTriggers.contains(fa.field) =>
        val (axioms, trigs, _, smDef) = generateFieldTrigger(fa, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
        smDefs = smDefs ++ smDef
      case pa: ast.PredicateAccess if s.heapDependentTriggers.contains(pa.loc(s.program)) =>
        val (axioms, trigs, _, smDef) = generatePredicateTrigger(pa, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
        smDefs = smDefs ++ smDef
      case wand: ast.MagicWand if s.heapDependentTriggers.contains(MagicWandIdentifier(wand, s.program)) =>
        val (axioms, trigs, _, smDef) = generateWandTrigger(wand, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
        smDefs = smDefs ++ smDef
      case e => evalTrigger(s, Seq(e), pve, v)((_, t, _) => {
        triggers = triggers ++ t
        Success()
      })
    }

    val triggerString = exps.mkString(", ")
    v.decider.assume(triggerAxioms, Option.when(withExp)(DebugExp.createInstance(s"Heap Triggers ($triggerString)")), enforceAssumption = false)
    var fr = s.functionRecorder
    for (smDef <- smDefs){
      fr = fr.recordFvfAndDomain(smDef)
    }
    Q(s.copy(functionRecorder = fr), triggers, v)
  }

  private def generateFieldTrigger(fa: ast.FieldAccess,
                                   s: State,
                                   pve: PartialVerificationError,
                                   v: Verifier)
                                  : (Seq[Term], Seq[Term], FieldTrigger, Seq[SnapshotMapDefinition]) = {

    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: FieldTrigger = null
    val codomainQVars = Seq(`?r`)
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s.h, BasicChunkIdentifier(fa.field.name))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, fa.field, codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)

    var smRes = Seq(smDef1)
    /* TODO: Reduce code duplication below */
    /* TODO: Return updated snapshot caches (or let generateFieldTrigger take a continuation) */

    fa.rcv match {
      case acc: ast.FieldAccess =>
        /* TODO: Is this *recursive* case even necessary? Wouldn't the eval(...) in the other case
         *       recurse anyway?
         */
        val rcvHelper = generateFieldTrigger(acc, s, pve, v)
        val rcvTrig = rcvHelper._3
        axioms = axioms ++ smDef1.valueDefinitions ++ rcvHelper._1
        mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, Lookup(rcvTrig.field, rcvTrig.fvf, rcvTrig.at))
        triggers = triggers ++ rcvHelper._2 :+ mostRecentTrig
        smRes = smRes ++ rcvHelper._4
      case rcv =>
        val s1 = s.copy(smCache = smCache1)
        val t = s1.possibleTriggers.get(fa)
        t match { /* TODO: r isn't used - why? */
          case Some(cachedTrigger) =>
            cachedTrigger match {
              case l: Lookup =>
                axioms = axioms ++ smDef1.valueDefinitions
                mostRecentTrig = FieldTrigger(l.field, smDef1.sm, l.at)
                triggers = triggers :+ mostRecentTrig
              case _ =>
                eval(s1.copy(triggerExp = true), rcv, pve, v)((_, tRcv, _, _) => {
                  axioms = axioms ++ smDef1.valueDefinitions
                  mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, tRcv)
                  triggers = triggers :+ mostRecentTrig
                  Success()
                })
            }
          case None =>
            eval(s1.copy(triggerExp = true), rcv, pve, v)((_, tRcv, _, _) => {
              axioms = axioms ++ smDef1.valueDefinitions
              mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, tRcv)
              triggers = triggers :+ mostRecentTrig
              Success()
            })
        }
    }

    (axioms, triggers, mostRecentTrig, smRes)
  }

  /* TODO: Try to unify with generateFieldTrigger above, or at least with generateWandTrigger below */
  private def generatePredicateTrigger(pa: ast.PredicateAccess,
                                       s: State,
                                       pve: PartialVerificationError,
                                       v: Verifier)
                                      : (Seq[Term], Seq[Term], PredicateTrigger, Seq[SnapshotMapDefinition]) = {
    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: PredicateTrigger = null
    val codomainQVars = s.predicateFormalVarMap(pa.loc(s.program))
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s.h, BasicChunkIdentifier(pa.predicateName))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, pa.loc(s.program), codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)
    val s1 = s.copy(smCache = smCache1)

    evals(s1, pa.args, _ => pve, v)((_, tArgs, _, _) => {
      axioms = axioms ++ smDef1.valueDefinitions
      mostRecentTrig = PredicateTrigger(pa.predicateName, smDef1.sm, tArgs)
      triggers = triggers :+ mostRecentTrig
      Success()
    })

    (axioms, triggers, mostRecentTrig, Seq(smDef1))
  }

  /* TODO: See comments for generatePredicateTrigger above */
  private def generateWandTrigger(wand: ast.MagicWand,
                                  s: State,
                                  pve: PartialVerificationError,
                                  v: Verifier)
                                 : (Seq[Term], Seq[Term], PredicateTrigger, Seq[SnapshotMapDefinition]) = {
    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: PredicateTrigger = null
    val wandHoles = wand.subexpressionsToEvaluate(s.program)
    val codomainQVars =
      wandHoles.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(wandHoles(i).typ), false))
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s.h, MagicWandIdentifier(wand, s.program))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, wand, codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)
    val s1 = s.copy(smCache = smCache1)

    evals(s1, wand.subexpressionsToEvaluate(s.program), _ => pve, v)((_, tArgs, _, _) => {
      axioms = axioms ++ smDef1.valueDefinitions
      mostRecentTrig = PredicateTrigger(MagicWandIdentifier(wand, s.program).toString, smDef1.sm, tArgs)
      triggers = triggers :+ mostRecentTrig
      Success()
    })

    (axioms, triggers, mostRecentTrig, Seq(smDef1))
  }

  /* Evaluate a sequence of expressions in Order
   * The constructor determines when the evaluation stops
   * Only Or and And are supported for the constructor
   */
  private def evalSeqShortCircuit(constructor: Seq[Term] => Term,
                                  s: State,
                                  exps: Seq[ast.Exp],
                                  pve: PartialVerificationError,
                                  v: Verifier)
                                 (Q: (State, Term, Option[ast.Exp], Verifier) => VerificationResult)
                                 : VerificationResult = {
    assert(
      constructor == Or || constructor == And,
      "Only Or and And are supported as constructors for evalSeqShortCircuit")

    assert(exps.nonEmpty, "Empty sequence of expressions not allowed")

    val stop = if (constructor == Or) True else False

    eval(s, exps.head, pve, v)((s1, t0, e0New, v1) => {
      t0 match {
        case _ if exps.tail.isEmpty => Q(s1, t0, e0New, v1) // Done, if no expressions left (necessary)
        case `stop` => Q(s1, t0, e0New, v1) // Done, if last expression was true/false for or/and (optimisation)
        case _ =>
          val expPair = if (constructor == Or) (exps.head, e0New) else (ast.Not(exps.head)(), e0New.map(ast.Not(_)()))
          joiner.join[(Term, Option[ast.Exp]), (Term, Option[ast.Exp])](s1, v1)((s2, v2, QB) =>
            brancher.branch(s2.copy(parallelizeBranches = false), if (constructor == Or) t0 else Not(t0), expPair, v2, fromShortCircuitingAnd = true)(
              (s3, v3) => QB(s3.copy(parallelizeBranches = s2.parallelizeBranches), (t0, e0New), v3),
              (s3, v3) => evalSeqShortCircuit(constructor, s3.copy(parallelizeBranches = s2.parallelizeBranches), exps.tail, pve, v3)((s2, t2, e2, v2) => QB(s2, (t2, e2), v2)))
            ){case Seq(ent) =>
                (ent.s, ent.data)
              case Seq(ent1, ent2) =>
                val exp = Option.when(withExp)({
                  if (constructor == Or)
                    ast.Or(ent1.data._2.get, ent2.data._2.get)()
                  else
                    ast.And(ent1.data._2.get, ent2.data._2.get)()
                })
                (ent1.s.merge(ent2.s), (constructor(Seq(ent1.data._1, ent2.data._1)), exp))
              case entries =>
                sys.error(s"Unexpected join data entries $entries")
            }((s3, r3, v3) => {
            val (t3, e3) = r3
            Q(s3, t3, e3, v3)
          })
      }})
  }

  private[silicon] case object FromShortCircuitingAnd extends ast.Info {
    val comment = Nil
    val isCached = false
  }
}
