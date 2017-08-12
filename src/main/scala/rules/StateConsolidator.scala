/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import scala.collection.mutable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state._
import viper.silicon.verifier.Verifier

trait StateConsolidationRules extends SymbolicExecutionRules {
  def consolidate(s: State, v: Verifier): State
  def consolidateIfRetrying(s: State, v: Verifier): State
  def merge(h: Heap, ch: PermissionChunk, v: Verifier): (Heap, Option[PermissionChunk])
  def merge(h: Heap, newH: Heap, v: Verifier): Heap
}

object stateConsolidator extends StateConsolidationRules with Immutable {
  def consolidate(s: State, v: Verifier): State = {
    v.decider.prover.comment("[state consolidation]")
    v.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.beforeIteration)

    val (permissionChunks, otherChunk) = partition(s.h)

    var continue = false

    var mergedChunks: Seq[PermissionChunk] = Nil
    var destChunks: Seq[PermissionChunk] = Nil
    var newChunks: Seq[PermissionChunk] = permissionChunks

    do {
      val (_mergedChunks, _, snapEqs) = singleMerge(destChunks, newChunks, v)

      snapEqs foreach v.decider.assume

      mergedChunks = _mergedChunks
      destChunks = Nil
      newChunks = mergedChunks
      continue = snapEqs.nonEmpty
    } while(continue)

    assumeValidPermissionAmounts(mergedChunks, v)

    val referenceIneqs = computeUpperPermissionBoundAssumptions(mergedChunks, v)

    v.decider.prover.comment("assuming upper bounds for field permissions")
    v.decider.assume(referenceIneqs)

    s.copy(h = Heap(mergedChunks ++ otherChunk))
  }

  def consolidateIfRetrying(s: State, v: Verifier): State =
    if (s.retrying) consolidate(s, v)
    else s

  def merge(h: Heap, ch: PermissionChunk, v: Verifier): (Heap, Option[PermissionChunk]) = {
    val (permissionChunks, otherChunk) = partition(h)
    val (mergedChunks, matches, snapEqs) = singleMerge(permissionChunks, ch :: Nil, v)

    v.decider.assume(snapEqs)

    val optMatch = ch match {
      case ch: PermissionChunk => matches.get(ch)
      case _ => None
    }

    (Heap(mergedChunks ++ otherChunk), optMatch)
  }

  def merge(h: Heap, newH: Heap, v: Verifier): Heap = {
    val (permissionChunks, otherChunk) = partition(h)
    val (newPermissionChunks, newOtherChunk) = partition(newH)
    val (mergedChunks, _, snapEqs) = singleMerge(permissionChunks, newPermissionChunks, v)

    v.decider.assume(snapEqs)

    Heap(mergedChunks ++ otherChunk ++ newOtherChunk)
  }

  private def singleMerge(destChunks: Seq[PermissionChunk], newChunks: Seq[PermissionChunk], v: Verifier)
                         : (Seq[PermissionChunk], Map[PermissionChunk, PermissionChunk], InsertionOrderedSet[Term]) = {

//    bookkeeper.heapMergeIterations += 1

    /* TODO: Fix `matches` map - subsequent matches override previous matches! */

    val (mergedChunks, matches, tSnaps) = {
      val initial = (destChunks, Map[PermissionChunk, PermissionChunk](), InsertionOrderedSet[Term]())

      newChunks.foldLeft(initial) { case ((accMergedChunks, accMatches, accSnapEqs), newChunk) =>
        /* accMergedChunks: already merged chunks
         * accMatches: records
         * accSnapEqs: collected snapshot equalities
         * newChunk: current chunk from the sequence of new chunks/of chunks to merge into the
         *           sequence of destination chunks
         */

        newChunk match {
          case ch2: BasicChunk =>
            chunkSupporter.getChunk(accMergedChunks, ch2.name, ch2.args, v) match {
              case Some(ch1: BasicChunk) if ch1.getClass == ch2.getClass =>
                val (tSnap, tSnapEq) = combineSnapshots(ch1.snap, ch2.snap, ch1.perm, ch2.perm, v)
                val c3 = ch1.duplicate(perm = PermPlus(ch1.perm, ch2.perm), snap = tSnap)

                (c3 +: accMergedChunks.filterNot(_ == ch1), accMatches + (ch1 -> ch2), accSnapEqs + tSnapEq)

              case Some(ch1) =>
                sys.error(
                  s"""Chunks
                     |  ch1 = $ch1
                     |  ch2 = $ch2
                     |of classes
                     |  ch1 = ${ch1.getClass.getName},
                     |  ch2 = ${ch2.getClass.getName}
                     |were not expected to appear in heaps
                     |  dest = $destChunks,
                     |  new = $newChunks.""".stripMargin)

              case None =>
                (ch2 +: accMergedChunks, accMatches, accSnapEqs)
            }

          case ch2: QuantifiedFieldChunk =>
            (ch2 +: accMergedChunks, accMatches, accSnapEqs)

          case ch2: QuantifiedPredicateChunk =>
            (ch2 +: accMergedChunks, accMatches, accSnapEqs)
        }
      }
    }

    (mergedChunks, matches, tSnaps)
  }

  private def combineSnapshots(t1: Term, t2: Term, p1: Term, p2: Term, v: Verifier): (Term, Term) = {
    val (tSnap, tSnapDef) =
      (IsPositive(p1), IsPositive(p2)) match {
        case (True(), b2) => (t1, Implies(b2, t1 === t2))
        case (b1, True()) => (t2, Implies(b1, t2 === t1))
        case (b1, b2) =>
          val t3 = v.decider.fresh(t1.sort)
          (t3,  And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
      }

    (tSnap, tSnapDef)
  }

  /* Compute assumptions capturing that a valid field permission amount cannot exceed write permission */
  private def computeUpperPermissionBoundAssumptions(chs: Seq[PermissionChunk], v: Verifier): List[Term] = {
//    bookkeeper.objectDistinctnessComputations += 1

    val pairsPerField = mutable.HashMap[String, mutable.ListBuffer[(Term, Term)]]()
//    val pairsPerFieldQP = mutable.HashMap[String, mutable.ListBuffer[Term]]()

    def add(fieldName: String, rcvr: Term, perm: Term) {
      pairsPerField.getOrElseUpdate(fieldName, mutable.ListBuffer[(Term, Term)]())
                   .append((rcvr, perm))
    }

//    def addQP(fieldName: String, perm: Term) {
//      pairsPerFieldQP.getOrElseUpdate(fieldName, mutable.ListBuffer[Term]())
//                     .append(perm)
//    }

    chs foreach {
      case FieldChunk(rcvr, fieldName, _, perm) =>
        add(fieldName, rcvr, perm)
      case QuantifiedFieldChunk(fieldName, _, perm, _, _, Some(rcvr), _) =>
        /* Singleton quantified chunks are treated analogous to non-quantified chunks */
        add(fieldName, rcvr, perm.replace(`?r`, rcvr))
//      case QuantifiedFieldChunk(fieldName, _, perm, _, _, _, _) =>
//        addQP(fieldName, perm)
      case _ =>
    }

    val tAssumptions = mutable.ListBuffer[Term]()

    for ((_, pairs) <- pairsPerField;
         Seq((rcvr1, perm1), (rcvr2, perm2)) <- pairs.combinations(2)) {

      if (   rcvr1 != rcvr2 /* Not essential for soundness, but avoids fruitless prover calls */
          && v.decider.check(PermLess(FullPerm(), PermPlus(perm1, perm2)), Verifier.config.checkTimeout())) {

        tAssumptions += (rcvr1 !== rcvr2)
      }
    }

//    val r1 = Var(Identifier("r1"), sorts.Ref)
//    val r2 = Var(Identifier("r2"), sorts.Ref)
//    var rs = Seq(r1, r2)
//
//    for ((field, perms) <- pairsPerFieldQP;
//         Seq(p1, p2) <- perms.combinations(2);
//         perm1 = p1.replace(`?r`, r1);
//         perm2 = p2.replace(`?r`, r2)) {
//
//      tAssumptions += Forall(rs, Implies(r1 === r2, PermAtMost(PermPlus(perm1, perm2), FullPerm())), Nil).autoTrigger
//        /* TODO: Give each quantifier a unique QID */
//        /* TODO: Body probably won't contain any (good) triggers - we need a field access trigger! */
//    }

    tAssumptions.result()
  }

  private def assumeValidPermissionAmounts(chs: Seq[PermissionChunk], v: Verifier) {
    chs foreach {
      case fc: FieldChunk => v.decider.assume(PermAtMost(fc.perm, FullPerm()))
      case _=>
    }
  }

  @inline
  final private def partition(h: Heap): (Seq[PermissionChunk], Seq[Chunk]) = {
    var permissionChunks = Seq[PermissionChunk]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: PermissionChunk => permissionChunks +:= ch
      case ch => otherChunks +:= ch
    }

    (permissionChunks, otherChunks)
  }
}
