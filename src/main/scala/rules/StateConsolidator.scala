// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state._
import viper.silicon.logger.records.data.{CommentRecord, SingleMergeRecord}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.functions.FunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.parser.PUnknown

import scala.annotation.unused

trait StateConsolidationRules extends SymbolicExecutionRules {
  def consolidate(s: State, v: Verifier): State
  def consolidateOptionally(s: State, v: Verifier): State
  def merge(fr: FunctionRecorder, s: State, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap)
  def merge(fr: FunctionRecorder, s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap)

  protected def assumeUpperPermissionBoundForQPFields(s: State, v: Verifier): State
  protected def assumeUpperPermissionBoundForQPFields(s: State, heaps: Seq[Heap], v: Verifier): State
}

/** Performs the minimal work necessary for any consolidator: merging two heaps combines the chunk
  * collections, but does not merge any chunks or deduce any additional information, e.g. from
  * permission values. All other operations (state consolidation, assuming QP permission bounds)
  * are no-ops.
  */
class MinimalStateConsolidator extends StateConsolidationRules {
  def consolidate(s: State, @unused v: Verifier): State = s
  def consolidateOptionally(s: State, @unused v: Verifier): State = s

  def merge(fr: FunctionRecorder, s: State, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) =
    (fr, Heap(h.values ++ newH.values))

  def merge(fr: FunctionRecorder, s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) =
    (fr, h + ch)

  protected def assumeUpperPermissionBoundForQPFields(s: State, @unused v: Verifier): State = s

  protected def assumeUpperPermissionBoundForQPFields(s: State, @unused heaps: Seq[Heap], @unused v: Verifier): State = s
}

/** Default implementation that merges as many known-alias chunks as possible, and deduces various
  * additional properties from and about permissions, (non)aliasing, and field values.
  */
class DefaultStateConsolidator(protected val config: Config) extends StateConsolidationRules {
  def consolidate(s: State, v: Verifier): State = {
    val comLog = new CommentRecord("state consolidation", s, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(comLog)
    v.decider.prover.comment("[state consolidation]")
    v.decider.prover.saturate(config.proverSaturationTimeouts.beforeIteration)

    val initialHeaps = s.h +: s.reserveHeaps

    val (functionRecorderAfterHeapMerging, mergedHeaps) =
      initialHeaps.foldLeft((s.functionRecorder, Nil: List[Heap])) { case ((fr, hs), h) =>
        var continue = false

        var mergedChunks: Seq[Chunk] = Nil
        var destChunks: Seq[Chunk] = Nil
        var newChunks: Seq[Chunk] = h.values.toSeq
        var functionRecorder: FunctionRecorder = fr

        var fixedPointRound: Int = 0
        do {
          val roundLog = new CommentRecord("Round " + fixedPointRound, s, v.decider.pcs)
          val roundSepIdentifier = v.symbExLog.openScope(roundLog)

          val (_functionRecorder, _mergedChunks, _, snapEqs) = singleMerge(functionRecorder, destChunks, newChunks, s.functionRecorderQuantifiedVariables().map(_._1), v)

          snapEqs foreach (t => v.decider.assume(t, Option.when(withExp)(DebugExp.createInstance("Snapshot Equations", true))))

          functionRecorder = _functionRecorder
          mergedChunks = _mergedChunks
          destChunks = Nil
          newChunks = mergedChunks
          continue = snapEqs.nonEmpty

          v.symbExLog.closeScope(roundSepIdentifier)
          fixedPointRound = fixedPointRound + 1
        } while (continue)


        val interpreter = new NonQuantifiedPropertyInterpreter(mergedChunks, v)

        mergedChunks.filter(_.isInstanceOf[BasicChunk]) foreach { case ch: BasicChunk =>
          val resource = Resources.resourceDescriptions(ch.resourceID)
          val pathCond = interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties(s.mayAssumeUpperBounds))
          pathCond.foreach(p => v.decider.assume(p._1, Option.when(withExp)(DebugExp.createInstance(p._2, p._2))))
        }

        Resources.resourceDescriptions foreach { case (id, desc) =>
          val pathCond = interpreter.buildPathConditionsForResource(id, desc.delayedProperties(s.mayAssumeUpperBounds))
          pathCond.foreach(p => v.decider.assume(p._1, Option.when(withExp)(DebugExp.createInstance(p._2, p._2))))
        }

        v.symbExLog.closeScope(sepIdentifier)
        (functionRecorder, hs :+ Heap(mergedChunks))
      }

    val s1 = s.copy(functionRecorder = functionRecorderAfterHeapMerging,
                    h = mergedHeaps.head,
                    reserveHeaps = mergedHeaps.tail)

    val s2 = assumeUpperPermissionBoundForQPFields(s1, v)

    s2
  }

  def consolidateOptionally(s: State, v: Verifier): State =
    if (s.retrying) consolidate(s, v)
    else s

  def merge(fr: FunctionRecorder, s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) = {
    merge(fr, s, h, Heap(Seq(ch)), v)
  }

  def merge(fr1: FunctionRecorder, s: State, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) = {
    val mergeLog = new CommentRecord("Merge", null, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(mergeLog)
    val (fr2, mergedChunks, newlyAddedChunks, snapEqs) = singleMerge(fr1, h.values.toSeq, newH.values.toSeq, s.functionRecorderQuantifiedVariables().map(_._1), v)

    v.decider.assume(snapEqs, Option.when(withExp)(DebugExp.createInstance("Snapshot", isInternal_ = true)), enforceAssumption = false)

    val interpreter = new NonQuantifiedPropertyInterpreter(mergedChunks, v)
    newlyAddedChunks.filter(_.isInstanceOf[BasicChunk]) foreach { case ch: BasicChunk =>
      val resource = Resources.resourceDescriptions(ch.resourceID)
      val pathCond = interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties(s.mayAssumeUpperBounds))
      pathCond.foreach(p => v.decider.assume(p._1, Option.when(withExp)(DebugExp.createInstance(p._2, p._2))))
    }

    v.symbExLog.closeScope(sepIdentifier)
    (fr2, Heap(mergedChunks))
  }

  private def singleMerge(fr: FunctionRecorder,
                          destChunks: Seq[Chunk],
                          newChunks: Seq[Chunk],
                          qvars: Seq[Var],
                          v: Verifier)
                         : (FunctionRecorder,
                            Seq[Chunk],
                            Seq[Chunk],
                            InsertionOrderedSet[Term]) = {

    val mergeLog = new SingleMergeRecord(destChunks, newChunks, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(mergeLog)
    // bookkeeper.heapMergeIterations += 1

    val initial = (fr, destChunks, Seq[Chunk](), InsertionOrderedSet[Term]())

    val result = newChunks.foldLeft(initial) { case ((fr1, accMergedChunks, accNewChunks, accSnapEqs), nextChunk) =>
      /* accMergedChunks: already merged chunks
       * accNewChunks: newly added chunks
       * accSnapEqs: collected snapshot equalities
       * nextChunk: current chunk from the sequence of new chunks/of chunks to merge into the
       *           sequence of destination chunks
       */

      findMatchingChunk(accMergedChunks, nextChunk, v) match {
        case Some(ch) =>
          mergeChunks(fr1, ch, nextChunk, qvars, v) match {
            case Some((fr2, newChunk, snapEq)) =>
              (fr2, newChunk +: accMergedChunks.filterNot(_ == ch), newChunk +: accNewChunks, accSnapEqs + snapEq)
            case None =>
              (fr1, nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accSnapEqs)
          }
        case None =>
          (fr1, nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accSnapEqs)
      }
    }
    v.symbExLog.closeScope(sepIdentifier)
    result
  }

  private def findMatchingChunk(chunks: Iterable[Chunk], chunk: Chunk, v: Verifier): Option[Chunk] = {
    chunk match {
      case chunk: BasicChunk =>
        chunkSupporter.findChunk[BasicChunk](chunks, chunk.id, chunk.args, v)
      case chunk: QuantifiedChunk => quantifiedChunkSupporter.findChunk(chunks, chunk, v)
      case _ => None
    }
  }

  // Merges two chunks that are aliases (i.e. that have the same id and the args are proven to be equal)
  // and returns the merged chunk or None, if the chunks could not be merged
  private def mergeChunks(fr1: FunctionRecorder, chunk1: Chunk, chunk2: Chunk, qvars: Seq[Var], v: Verifier): Option[(FunctionRecorder, Chunk, Term)] = (chunk1, chunk2) match {
    case (BasicChunk(rid1, id1, args1, args1Exp, snap1, snap1Exp, perm1, perm1Exp), BasicChunk(_, _, _, _, snap2, _, perm2, perm2Exp)) =>
      val (fr2, combinedSnap, snapEq) = combineSnapshots(fr1, snap1, snap2, perm1, perm2, qvars, v)

      Some(fr2, BasicChunk(rid1, id1, args1, args1Exp, combinedSnap, snap1Exp, PermPlus(perm1, perm2), perm1Exp.map(p1 => ast.PermAdd(p1, perm2Exp.get)())), snapEq)
    case (l@QuantifiedFieldChunk(id1, fvf1, condition1, condition1Exp,  perm1, perm1Exp, invs1, singletonRcvr1, singletonRcvr1Exp, hints1),
          r@QuantifiedFieldChunk(_, fvf2, _, _, perm2, perm2Exp, _, _, _, hints2)) =>
      assert(l.quantifiedVars == Seq(`?r`))
      assert(r.quantifiedVars == Seq(`?r`))
      // We need to use l.perm/r.perm here instead of perm1 and perm2 since the permission amount might be dependent on the condition/domain
      val (fr2, combinedSnap, snapEq) = quantifiedChunkSupporter.combineFieldSnapshotMaps(fr1, id1.name, fvf1, fvf2, l.perm, r.perm, v)
      val permSum = PermPlus(perm1, perm2)
      val permSumExp = perm1Exp.map(p1 => ast.PermAdd(p1, perm2Exp.get)())
      val bestHints = if (hints1.nonEmpty) hints1 else hints2
      Some(fr2, QuantifiedFieldChunk(id1, combinedSnap, condition1, condition1Exp, permSum, permSumExp, invs1, singletonRcvr1, singletonRcvr1Exp, bestHints), snapEq)
    case (l@QuantifiedPredicateChunk(id1, qVars1, qVars1Exp, psf1, _, _, perm1, perm1Exp, _, _, _, _),
          r@QuantifiedPredicateChunk(_, qVars2, qVars2Exp, psf2, condition2, condition2Exp, perm2, perm2Exp, invs2, singletonArgs2, singletonArgs2Exp, hints2)) =>
      val (fr2, combinedSnap, snapEq) = quantifiedChunkSupporter.combinePredicateSnapshotMaps(fr1, id1.name, qVars2, psf1, psf2, l.perm.replace(qVars1, qVars2), r.perm, v)

      val permSum = PermPlus(perm1.replace(qVars1, qVars2), perm2)
      val permSumExp = perm1Exp.map(p1 => ast.PermAdd(p1.replace(qVars1Exp.get.zip(qVars2Exp.get).toMap), perm2Exp.get)())
      Some(fr2, QuantifiedPredicateChunk(id1, qVars2, qVars2Exp, combinedSnap, condition2, condition2Exp, permSum, permSumExp, invs2, singletonArgs2, singletonArgs2Exp, hints2), snapEq)
    case _ =>
      None
  }

  /** Merge the snapshots of two chunks that denote the same location, i.e. whose ids and arguments
    * are known to be equal.
    *
    * @param fr The functionRecorder to use when new snapshots are generated.
    * @param t1 The first chunk's snapshot.
    * @param t2 The second chunk's snapshot.
    * @param p1 The first chunk's permission amount.
    * @param p2 The second chunk's permission amount.
    * @param qvars Quantified variables in the current context.
    * @param v The verifier to use.
    * @return A tuple (fr, snap, def) of functionRecorder, a snapshot snap and a term def constraining snap.
    */
  private def combineSnapshots(fr: FunctionRecorder, t1: Term, t2: Term, p1: Term, p2: Term, qvars: Seq[Var], v: Verifier): (FunctionRecorder, Term, Term) = {
    (IsPositive(p1), IsPositive(p2)) match {
      case (True, b2) => (fr, t1, Implies(b2, t1 === t2))
      case (b1, True) => (fr, t2, Implies(b1, t2 === t1))
      case (b1, b2) =>
        /*
         * Since it is not definitely known whether p1 and p2 are positive,
         * we have to introduce a fresh snapshot. Note that it is not sound
         * to use t1 or t2 and constrain it.
         */
        val t3 = v.decider.appliedFresh("ms", t1.sort, qvars)
        val newFr = fr.recordPathSymbol(t3.applicable.asInstanceOf[Function]).recordConstraint(And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
        (newFr, t3, And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
    }
  }

  protected def assumeUpperPermissionBoundForQPFields(s: State, v: Verifier): State =
    assumeUpperPermissionBoundForQPFields(s, s.h +: s.reserveHeaps, v)

  protected def assumeUpperPermissionBoundForQPFields(s: State, heaps: Seq[Heap], v: Verifier): State = {
    heaps.foldLeft(s) { case (si, heap) =>
      val chunks: Seq[QuantifiedFieldChunk] =
        heap.values.collect({ case ch: QuantifiedFieldChunk => ch }).to(Seq)

      val receiver = `?r`
      val receiverExp = ast.LocalVarDecl(receiver.id.name, ast.Ref)()
      val args = Seq(receiver)
      val chunksPerField: Map[String, Seq[QuantifiedFieldChunk]] = chunks.groupBy(_.id.name)

      /* Iterate over all fields f and effectively assume "forall x :: {x.f} perm(x.f) <= write"
         for each field. Nearly identical to what the evaluator does for perm(x.f) if f is
         a QP field */
      chunksPerField.foldLeft(si) { case (si, (fieldName, fieldChunks)) =>
        val field = s.program.findField(fieldName)
        val (sn, smDef, pmDef) =
          quantifiedChunkSupporter.heapSummarisingMaps(si, field, args, fieldChunks, v)
        var sf = sn

        if (sn.heapDependentTriggers.exists(r => r.isInstanceOf[ast.Field] && r.asInstanceOf[ast.Field].name == fieldName)) {
          val trigger = FieldTrigger(field.name, smDef.sm, receiver)
          val currentPermAmount = PermLookup(field.name, pmDef.pm, receiver)
          v.decider.prover.comment(s"Assume upper permission bound for field ${field.name}")

          val debugExp = if (withExp) {
            val (debugHeapName, debugLabel) = v.getDebugOldLabel(sn, ast.NoPosition)
            sf = sf.copy(oldHeaps = sf.oldHeaps + (debugHeapName -> sf.h))
            val permExp = ast.DebugLabelledOld(ast.CurrentPerm(ast.FieldAccess(receiverExp.localVar, field)())(ast.NoPosition, ast.NoInfo, ast.NoTrafos), debugLabel)()
            val exp = ast.Forall(Seq(receiverExp), Seq(), ast.PermLeCmp(permExp, ast.FullPerm()())())()
            Some(DebugExp.createInstance(exp, exp))
          } else { None }
          v.decider.assume(
            Forall(receiver, PermAtMost(currentPermAmount, FullPerm), Trigger(trigger), "qp-fld-prm-bnd"), debugExp)
        } else {
          /*
          If we don't use heap-dependent triggers, the trigger x.f does not work. Instead, we assume the permission
          bound explicitly for each singleton chunk receiver, and for each chunk, triggering on its inverse functions.
          That is, we assume
          forall r: Ref :: {inv(r)} perm(x.f) <= write
           */
          for (chunk <- fieldChunks) {
            if (chunk.singletonRcvr.isDefined){
              val debugExp = if (withExp) {
                val (debugHeapName, debugLabel) = v.getDebugOldLabel(sn, ast.NoPosition)
                val permExp = ast.DebugLabelledOld(ast.CurrentPerm(ast.FieldAccess(chunk.singletonRcvrExp.get, field)())(), debugLabel)()
                sf = sf.copy(oldHeaps = sf.oldHeaps + (debugHeapName -> sf.h))
                val exp = ast.PermLeCmp(permExp, ast.FullPerm()())()
                Some(DebugExp.createInstance(exp, exp))
              } else { None }
              v.decider.assume(PermAtMost(PermLookup(field.name, pmDef.pm, chunk.singletonRcvr.get), FullPerm), debugExp)
            } else {
              val chunkReceivers = chunk.invs.get.inverses.map(i => App(i, chunk.invs.get.additionalArguments ++ chunk.quantifiedVars))
              val triggers = chunkReceivers.map(r => Trigger(r)).toSeq
              val currentPermAmount = PermLookup(field.name, pmDef.pm, chunk.quantifiedVars.head)
              v.decider.prover.comment(s"Assume upper permission bound for field ${field.name}")
              val debugExp = if (withExp) {
                val chunkReceiverExp = chunk.quantifiedVarExps.get.head.localVar
                var permExp: ast.Exp = ast.CurrentPerm(ast.FieldAccess(chunkReceiverExp, field)())(chunkReceiverExp.pos, chunkReceiverExp.info, chunkReceiverExp.errT)
                val (debugHeapName, debugLabel) = v.getDebugOldLabel(sn, ast.NoPosition)
                sf = sf.copy(oldHeaps = sf.oldHeaps + (debugHeapName -> sf.h))
                permExp = ast.DebugLabelledOld(permExp, debugLabel)()
                val exp = ast.Forall(chunk.quantifiedVarExps.get, Seq(), ast.PermLeCmp(permExp, ast.FullPerm()())())()
                Some(DebugExp.createInstance(exp, exp))
              } else { None }
              v.decider.assume(
                Forall(chunk.quantifiedVars, PermAtMost(currentPermAmount, FullPerm), triggers, "qp-fld-prm-bnd"), debugExp)
            }

          }
        }

        sf
      }
    }
  }

  @inline
  private final def partition(h: Heap): (Seq[NonQuantifiedChunk], Seq[Chunk]) = {
    var nonQuantifiedChunks = Seq[NonQuantifiedChunk]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: NonQuantifiedChunk => nonQuantifiedChunks +:= ch
      case ch => otherChunks +:= ch
    }

    (nonQuantifiedChunks, otherChunks)
  }
}

/** A variant of [[DefaultStateConsolidator]]:
  *   - Merging heaps and assuming QP permission bounds is equally complete
  *   - State consolidation is equally complete, but only performed when Silicon is retrying
  *     an assertion/operation
  */
class RetryingStateConsolidator(config: Config) extends DefaultStateConsolidator(config) {
  override def consolidate(s: State, v: Verifier): State = {
    if (s.retrying) super.consolidate(s, v)
    else s
  }

  override def consolidateOptionally(s: State, v: Verifier): State = consolidate(s, v)
}

/** A variant of [[RetryingStateConsolidator]] that differs only in that optional state consolidations (i.e.,
  * ones not triggered by a verification failure) are not performed at all.
  */
class RetryingFailOnlyStateConsolidator(config: Config) extends RetryingStateConsolidator(config) {
  override def consolidateOptionally(s: State, v: Verifier): State = s
}

/** A variant of [[DefaultStateConsolidator]]:
  *   - Merging heaps and assuming QP permission bounds is equally complete
  *   - State consolidation is equally complete, but only performed when Silicon is retrying
  *     an assertion/operation for the last time.
  */
class LastRetryStateConsolidator(config: Config) extends DefaultStateConsolidator(config) {
  override def consolidate(s: State, v: Verifier): State = {
    if (s.isLastRetry) super.consolidate(s, v)
    else s
  }

  override def consolidateOptionally(s: State, v: Verifier): State = consolidate(s, v)
}

/** A variant of [[LastRetryStateConsolidator]] that differs only in that optional state consolidations (i.e.,
  * ones not triggered by a verification failure) are not performed at all.
  */
class LastRetryFailOnlyStateConsolidator(config: Config) extends LastRetryStateConsolidator(config) {
  override def consolidateOptionally(s: State, v: Verifier): State = s
}

/** A variant of [[RetryingStateConsolidator]] and [[MinimalStateConsolidator]]:
  *   - Consolidations are equivalent to [[RetryingStateConsolidator]]
  *   - Merging heaps and assuming QP permission bounds is equivalent to [[MinimalStateConsolidator]]
  */
class MinimalRetryingStateConsolidator(config: Config) extends RetryingStateConsolidator(config) {
  override def merge(fr: FunctionRecorder, s: State, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) =
    (fr, Heap(h.values ++ newH.values))

  override def merge(fr: FunctionRecorder, s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) =
    (fr, h + ch)

  override protected def assumeUpperPermissionBoundForQPFields(s: State, @unused v: Verifier): State = s

  override protected def assumeUpperPermissionBoundForQPFields(s: State, @unused heaps: Seq[Heap], @unused v: Verifier): State = s
}

/** A variant of [[DefaultStateConsolidator]] that aims to work best when Silicon is run in
  * more complete exhale mode:
  *   - Merging heaps and assuming QP permission bounds is equivalent to [[DefaultStateConsolidator]]
  *   - State consolidation is only performed when Silicon is retrying, and it only deduces
  *     assumptions about non-QP permission bounds
  *     (by calling [[moreCompleteExhaleSupporter.assumeFieldPermissionUpperBounds]])
  */
class MoreComplexExhaleStateConsolidator(config: Config) extends DefaultStateConsolidator(config) {
  override def consolidate(s: State, v: Verifier): State = {
    // NOTE: Skipping most of what the regular state consolidation performs results in
    // incompletenesses. E.g. when using quantified permissions, the state consolidation
    // will, among other things, assume non-aliasing for receivers of *singleton quantified
    // field chunks* whose permissions would sum up to more than full permission.
    // This, e.g. causes method test15 from test
    //   silver\src\test\resources\quantifiedpermissions\sets\generalised_shape.sil
    // to fail.

    if (s.retrying) {
      // TODO: apply to all heaps (s.h +: s.reserveHeaps, as done below)
      // NOTE: Doing this regardless of s.retrying might improve completeness in certain (rare) cases
      moreCompleteExhaleSupporter.assumeFieldPermissionUpperBounds(s.h, v)
    }

    s
  }
}
