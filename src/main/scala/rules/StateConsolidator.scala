/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state._
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms._
import viper.silicon.verifier.Verifier

trait StateConsolidationRules extends SymbolicExecutionRules {
  def consolidate(s: State, v: Verifier): State
  def consolidateIfRetrying(s: State, v: Verifier): State
  def merge(h: Heap, ch: NonQuantifiedChunk, v: Verifier): Heap
  def merge(h: Heap, newH: Heap, v: Verifier): Heap
}

object stateConsolidator extends StateConsolidationRules with Immutable {
  
  def consolidate(s: State, v: Verifier): State = {
    v.decider.prover.comment("[state consolidation]")
    v.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.beforeIteration)

    val heaps = s.h +: s.reserveHeaps
    val newHeaps = heaps.map { h =>
      val (nonQuantifiedChunks, otherChunks) = partition(h)

      var continue = false

      var mergedChunks: Seq[NonQuantifiedChunk] = Nil
      var destChunks: Seq[NonQuantifiedChunk] = Nil
      var newChunks: Seq[NonQuantifiedChunk] = nonQuantifiedChunks

      do {
        val (_mergedChunks, _, snapEqs) = singleMerge(destChunks, newChunks, v)

        snapEqs foreach v.decider.assume

        mergedChunks = _mergedChunks
        destChunks = Nil
        newChunks = mergedChunks
        continue = snapEqs.nonEmpty
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

      Heap(allChunks)
    }

    s.copy(h = newHeaps.head, reserveHeaps = newHeaps.tail)
  }

  def consolidateIfRetrying(s: State, v: Verifier): State =
    if (s.retrying) consolidate(s, v)
    else s

  def merge(h: Heap, ch: NonQuantifiedChunk, v: Verifier): Heap = merge(h, Heap(Seq(ch)), v)

  def merge(h: Heap, newH: Heap, v: Verifier): Heap = {
    val (nonQuantifiedChunks, otherChunks) = partition(h)
    val (newNonQuantifiedChunks, newOtherChunk) = partition(newH)
    val (mergedChunks, newlyAddedChunks, snapEqs) = singleMerge(nonQuantifiedChunks, newNonQuantifiedChunks, v)

    v.decider.assume(snapEqs)

    val interpreter = new NonQuantifiedPropertyInterpreter(mergedChunks, v)
    newlyAddedChunks foreach { ch =>
      val resource = Resources.resourceDescriptions(ch.resourceID)
      v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
    }

    Heap(mergedChunks ++ otherChunks ++ newOtherChunk)
  }

  private def singleMerge(destChunks: Seq[NonQuantifiedChunk], newChunks: Seq[NonQuantifiedChunk], v: Verifier)
                         : (Seq[NonQuantifiedChunk], Seq[NonQuantifiedChunk], InsertionOrderedSet[Term]) = {

    // bookkeeper.heapMergeIterations += 1

    val initial = (destChunks, Seq[NonQuantifiedChunk](), InsertionOrderedSet[Term]())

    newChunks.foldLeft(initial) { case ((accMergedChunks, accNewChunks, accSnapEqs), nextChunk) =>
      /* accMergedChunks: already merged chunks
       * accNewChunks: newly added chunks
       * accSnapEqs: collected snapshot equalities
       * nextChunk: current chunk from the sequence of new chunks/of chunks to merge into the
       *           sequence of destination chunks
       */

      chunkSupporter.findMatchingChunk(accMergedChunks, nextChunk, v) match {
        case Some(ch) =>
          mergeChunks(ch, nextChunk, v) match {
            case Some((newChunk, snapEq)) =>
              (newChunk +: accMergedChunks.filterNot(_ == ch), newChunk +: accNewChunks, accSnapEqs + snapEq)
            case None =>
              (nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accSnapEqs)
          }
        case None =>
          (nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accSnapEqs)
      }
    }
  }

  // Merges two chunks that are aliases (i.e. that have the same id and the args are proven to be equal)
  // and returns the merged chunk or None, if the chunks could not be merged
  private def mergeChunks(chunk1: NonQuantifiedChunk, chunk2: NonQuantifiedChunk, v: Verifier) = (chunk1, chunk2) match {
    case (BasicChunk(rid1, id1, args1, snap1, perm1), BasicChunk(_, _, _, snap2, perm2)) =>
      val (combinedSnap, snapEq) = combineSnapshots(snap1, snap2, perm1, perm2, v)
      Some(BasicChunk(rid1, id1, args1, combinedSnap, PermPlus(perm1, perm2)), snapEq)
    case (_, _) => None
  }

  private def combineSnapshots(t1: Term, t2: Term, p1: Term, p2: Term, v: Verifier): (Term, Term) = {
    val (tSnap, tSnapDef) =
      (IsPositive(p1), IsPositive(p2)) match {
        case (True(), b2) => (t1, Implies(b2, t1 === t2))
        case (b1, True()) => (t2, Implies(b1, t2 === t1))
        case (b1, b2) =>
          val t3 = v.decider.fresh(t1.sort)
          (t3, And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
      }

    (tSnap, tSnapDef)
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