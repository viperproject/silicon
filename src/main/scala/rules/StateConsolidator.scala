// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.annotation.unused
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

trait StateConsolidationRules extends SymbolicExecutionRules {
  def consolidate(s: State, v: Verifier): State
  def consolidateOptionally(s: State, v: Verifier): State
  def merge(fr: FunctionRecorder, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap)
  def merge(fr: FunctionRecorder, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap)

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

  def merge(fr: FunctionRecorder, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) =
    (fr, Heap(h.values ++ newH.values))

  def merge(fr: FunctionRecorder, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) =
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
        val (nonQuantifiedChunks, otherChunks) = partition(h)

        var continue = false

        var mergedChunks: Seq[NonQuantifiedChunk] = Nil
        var destChunks: Seq[NonQuantifiedChunk] = Nil
        var newChunks: Seq[NonQuantifiedChunk] = nonQuantifiedChunks
        var functionRecorder: FunctionRecorder = fr

        var fixedPointRound: Int = 0
        do {
          val roundLog = new CommentRecord("Round " + fixedPointRound, s, v.decider.pcs)
          val roundSepIdentifier = v.symbExLog.openScope(roundLog)

          val (_functionRecorder, _mergedChunks, _, snapEqs) = singleMerge(functionRecorder, destChunks, newChunks, v)

          snapEqs foreach v.decider.assume

          functionRecorder = _functionRecorder
          mergedChunks = _mergedChunks
          destChunks = Nil
          newChunks = mergedChunks
          continue = snapEqs.nonEmpty

          v.symbExLog.closeScope(roundSepIdentifier)
          fixedPointRound = fixedPointRound + 1
        } while (continue)

        val allChunks = mergedChunks ++ otherChunks
        val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v)

        mergedChunks foreach { ch =>
          val resource = Resources.resourceDescriptions(ch.resourceID)
          v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
        }

        Resources.resourceDescriptions foreach { case (id, desc) =>
          v.decider.assume(interpreter.buildPathConditionsForResource(id, desc.delayedProperties))
        }

        v.symbExLog.closeScope(sepIdentifier)
        (functionRecorder, hs :+ Heap(allChunks))
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

  def merge(fr: FunctionRecorder, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) = {
    merge(fr, h, Heap(Seq(ch)), v)
  }

  def merge(fr1: FunctionRecorder, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) = {
    val mergeLog = new CommentRecord("Merge", null, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(mergeLog)
    val (nonQuantifiedChunks, otherChunks) = partition(h)
    val (newNonQuantifiedChunks, newOtherChunk) = partition(newH)
    val (fr2, mergedChunks, newlyAddedChunks, snapEqs) = singleMerge(fr1, nonQuantifiedChunks, newNonQuantifiedChunks, v)

    v.decider.assume(snapEqs)

    val interpreter = new NonQuantifiedPropertyInterpreter(mergedChunks, v)
    newlyAddedChunks foreach { ch =>
      val resource = Resources.resourceDescriptions(ch.resourceID)
      v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
    }

    v.symbExLog.closeScope(sepIdentifier)
    (fr2, Heap(mergedChunks ++ otherChunks ++ newOtherChunk))
  }

  private def singleMerge(fr: FunctionRecorder,
                          destChunks: Seq[NonQuantifiedChunk],
                          newChunks: Seq[NonQuantifiedChunk],
                          v: Verifier)
                         : (FunctionRecorder,
                            Seq[NonQuantifiedChunk],
                            Seq[NonQuantifiedChunk],
                            InsertionOrderedSet[Term]) = {

    val mergeLog = new SingleMergeRecord(destChunks, newChunks, v.decider.pcs)
    val sepIdentifier = v.symbExLog.openScope(mergeLog)
    // bookkeeper.heapMergeIterations += 1

    val initial = (fr, destChunks, Seq[NonQuantifiedChunk](), InsertionOrderedSet[Term]())

    val result = newChunks.foldLeft(initial) { case ((fr1, accMergedChunks, accNewChunks, accSnapEqs), nextChunk) =>
      /* accMergedChunks: already merged chunks
       * accNewChunks: newly added chunks
       * accSnapEqs: collected snapshot equalities
       * nextChunk: current chunk from the sequence of new chunks/of chunks to merge into the
       *           sequence of destination chunks
       */

      chunkSupporter.findMatchingChunk(accMergedChunks, nextChunk, v) match {
        case Some(ch) =>
          mergeChunks(fr1, ch, nextChunk, v) match {
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

  // Merges two chunks that are aliases (i.e. that have the same id and the args are proven to be equal)
  // and returns the merged chunk or None, if the chunks could not be merged
  private def mergeChunks(fr1: FunctionRecorder, chunk1: NonQuantifiedChunk, chunk2: NonQuantifiedChunk, v: Verifier) = (chunk1, chunk2) match {
    case (BasicChunk(rid1, id1, args1, snap1, perm1), BasicChunk(_, _, _, snap2, perm2)) =>
      val (fr2, combinedSnap, snapEq) = combineSnapshots(fr1, snap1, snap2, perm1, perm2, v)

      Some(fr2, BasicChunk(rid1, id1, args1, combinedSnap, PermPlus(perm1, perm2)), snapEq)
    case (_, _) =>
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
    * @param v The verifier to use.
    * @return A tuple (fr, snap, def) of functionRecorder, a snapshot snap and a term def constraining snap.
    */
  private def combineSnapshots(fr: FunctionRecorder, t1: Term, t2: Term, p1: Term, p2: Term, v: Verifier): (FunctionRecorder, Term, Term) = {
    (IsPositive(p1), IsPositive(p2)) match {
      case (True, b2) => (fr, t1, Implies(b2, t1 === t2))
      case (b1, True) => (fr, t2, Implies(b1, t2 === t1))
      case (b1, b2) =>
        /*
         * Since it is not definitely known whether p1 and p2 are positive,
         * we have to introduce a fresh snapshot. Note that it is not sound
         * to use t1 or t2 and constrain it.
         */
        val t3 = v.decider.fresh(t1.sort)
        (fr.recordFreshSnapshot(t3), t3, And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
    }
  }

  protected def assumeUpperPermissionBoundForQPFields(s: State, v: Verifier): State =
    assumeUpperPermissionBoundForQPFields(s, s.h +: s.reserveHeaps, v)

  protected def assumeUpperPermissionBoundForQPFields(s: State, heaps: Seq[Heap], v: Verifier): State = {
    heaps.foldLeft(s) { case (si, heap) =>
      val chunks: Seq[QuantifiedFieldChunk] =
        heap.values.collect({ case ch: QuantifiedFieldChunk => ch }).to(Seq)

      val receiver = `?r`
      val args = Seq(receiver)
      val chunksPerField: Map[String, Seq[QuantifiedFieldChunk]] = chunks.groupBy(_.id.name)

      /* Iterate over all fields f and effectively assume "forall x :: {x.f} perm(x.f) <= write"
         for each field. Nearly identical to what the evaluator does for perm(x.f) if f is
         a QP field */
      chunksPerField.foldLeft(si) { case (si, (fieldName, fieldChunks)) =>
        val field = s.program.findField(fieldName)
        val (sn, smDef, pmDef) =
          quantifiedChunkSupporter.heapSummarisingMaps(si, field, args, fieldChunks, v)

        if (sn.heapDependentTriggers.exists(r => r.isInstanceOf[ast.Field] && r.asInstanceOf[ast.Field].name == fieldName)) {
          val trigger = FieldTrigger(field.name, smDef.sm, receiver)
          val currentPermAmount = PermLookup(field.name, pmDef.pm, receiver)
          v.decider.prover.comment(s"Assume upper permission bound for field ${field.name}")
          v.decider.assume(
            Forall(receiver, PermAtMost(currentPermAmount, FullPerm), Trigger(trigger), "qp-fld-prm-bnd"))
        } else {
          /*
          If we don't use heap-dependent triggers, the trigger x.f does not work. Instead, we assume the permission
          bound explicitly for each singleton chunk receiver, and for each chunk, triggering on its inverse functions.
          That is, we assume
          forall r: Ref :: {inv(r)} perm(x.f) <= write
           */
          for (chunk <- fieldChunks) {
            if (chunk.singletonRcvr.isDefined){
              v.decider.assume(PermAtMost(PermLookup(field.name, pmDef.pm, chunk.singletonRcvr.get), FullPerm))
            } else {
              val chunkReceivers = chunk.invs.get.inverses.map(i => App(i, chunk.invs.get.additionalArguments ++ chunk.quantifiedVars))
              val triggers = chunkReceivers.map(r => Trigger(r)).toSeq
              val currentPermAmount = PermLookup(field.name, pmDef.pm, chunk.quantifiedVars.head)
              v.decider.prover.comment(s"Assume upper permission bound for field ${field.name}")
              v.decider.assume(
                Forall(chunk.quantifiedVars, PermAtMost(currentPermAmount, FullPerm), triggers, "qp-fld-prm-bnd"))
            }

          }
        }

        sn
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
  override def merge(fr: FunctionRecorder, h: Heap, newH: Heap, v: Verifier): (FunctionRecorder, Heap) =
    (fr, Heap(h.values ++ newH.values))

  override def merge(fr: FunctionRecorder, h: Heap, ch: NonQuantifiedChunk, v: Verifier): (FunctionRecorder, Heap) =
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
