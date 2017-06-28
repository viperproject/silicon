/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state._
import viper.silicon.resources.{PropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier

import scala.collection.mutable

trait StateConsolidationRules extends SymbolicExecutionRules {
  def consolidate(s: State, v: Verifier): State
  def consolidateIfRetrying(s: State, v: Verifier): State
  def merge(h: Heap, ch: ResourceChunk, v: Verifier): (Heap, Option[ResourceChunk])
  def merge(h: Heap, newH: Heap, v: Verifier): Heap
}

object stateConsolidator extends StateConsolidationRules with Immutable {
  
  def consolidate(s: State, v: Verifier): State = {
    v.decider.prover.comment("[state consolidation]")

    val (resourceChunks, otherChunks) = partition(s.h)

    var continue = false

    var mergedChunks: Seq[ResourceChunk] = Nil
    var destChunks: Seq[ResourceChunk] = Nil
    var newChunks: Seq[ResourceChunk] = resourceChunks

    do {
      val (_mergedChunks, _,  _, snapEqs) = singleMerge(destChunks, newChunks, v)

      snapEqs foreach v.decider.assume

      mergedChunks = _mergedChunks
      destChunks = Nil
      newChunks = mergedChunks
      continue = snapEqs.nonEmpty
    } while(continue)

    val allChunks = mergedChunks ++ otherChunks

    val interpreter = new PropertyInterpreter(v, allChunks)
    Resources.resourceDescriptions foreach { case (id, desc) =>
      v.decider.prover.comment(s"Assuming delayed properties for $desc")
      v.decider.assume(interpreter.buildPathConditionsForResource(id, desc.delayedProperties))
    }

    mergedChunks foreach {
      case ch: ResourceChunk =>
        val resource = Resources.resourceDescriptions(ch.resourceID)
        v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
        v.decider.assume(interpreter.buildPathConditionsForResource(ch.resourceID, resource.staticProperties))
      case _ =>
    }

    // TODO: only here for quantified chunks
    v.decider.assume(computeUpperPermissionBoundAssumptions(otherChunks, v))

    s.copy(h = Heap(allChunks))
  }

  def consolidateIfRetrying(s: State, v: Verifier): State =
    if (s.retrying) consolidate(s, v)
    else s

  def merge(h: Heap, ch: ResourceChunk, v: Verifier): (Heap, Option[ResourceChunk]) = {
    val (mergedChunks, matches) = mergeHeaps(h, Heap(Seq(ch)), v)
    (mergedChunks, matches.get(ch))
  }

  def merge(h: Heap, newH: Heap, v: Verifier): Heap = mergeHeaps(h, newH, v)._1

  private def mergeHeaps(h: Heap, newH: Heap, v: Verifier): (Heap, Map[ResourceChunk, ResourceChunk]) = {
    val (resourceChunks, otherChunk) = partition(h)
    val (newResourceChunks, newOtherChunk) = partition(newH)
    val (mergedChunks, newlyAddedChunks,  matches, snapEqs) = singleMerge(resourceChunks, newResourceChunks, v)

    val interpreter = new PropertyInterpreter(v, mergedChunks)
    newlyAddedChunks foreach { ch =>
      val resource = Resources.resourceDescriptions(ch.resourceID)
      v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
      v.decider.assume(interpreter.buildPathConditionsForResource(ch.resourceID, resource.staticProperties))
    }
    v.decider.assume(snapEqs)

    (Heap(mergedChunks ++ otherChunk ++ newOtherChunk), matches)
  }

  private def singleMerge(destChunks: Seq[ResourceChunk], newChunks: Seq[ResourceChunk], v: Verifier)
  : (Seq[ResourceChunk], Seq[ResourceChunk], Map[ResourceChunk, ResourceChunk],
    InsertionOrderedSet[Term]) = {

    //    bookkeeper.heapMergeIterations += 1

    /* TODO: Fix `matches` map - subsequent matches override previous matches! */

    val initial = (destChunks, Seq[ResourceChunk](), Map[ResourceChunk, ResourceChunk](), InsertionOrderedSet[Term]())

    newChunks.foldLeft(initial) { case ((accMergedChunks, accNewChunks, accMatches, accSnapEqs), nextChunk) =>
      /* accMergedChunks: already merged chunks
       * accNewChunks: newly added chunks
       * accMatches: records
       * accSnapEqs: collected snapshot equalities
       * nextChunk: current chunk from the sequence of new chunks/of chunks to merge into the
       *           sequence of destination chunks
       */

      unifiedHeapSupporter.findMatchingChunk(accMergedChunks, nextChunk, v) match {
        case Some(ch) =>
          mergeChunks(ch, nextChunk, v) match {
            case Some((newChunk, snapEq)) =>
              (newChunk +: accMergedChunks.filterNot(_ == ch), newChunk +: accNewChunks, accMatches + (ch -> nextChunk), accSnapEqs + snapEq)
            case None =>
              (nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accMatches, accSnapEqs)
          }
        case None =>
          (nextChunk +: accMergedChunks, nextChunk +: accNewChunks, accMatches, accSnapEqs)
      }
    }
  }

  private def mergeChunks(chunk1: ResourceChunk, chunk2: ResourceChunk, v: Verifier) = (chunk1, chunk2) match {
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
          (t3,  And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
      }

    (tSnap, tSnapDef)
  }

  /* Compute assumptions capturing that a valid field permission amount cannot exceed write permission */
  private def computeUpperPermissionBoundAssumptions(chs: Seq[Chunk], v: Verifier): List[Term] = {
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
/*
      case BasicChunk(FieldID(), fieldName, args, _, perm) =>
        add(fieldName, args.head, perm)
*/
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

  @inline
  final private def partition(h: Heap): (Seq[ResourceChunk], Seq[Chunk]) = {
    var resourceChunks = Seq[ResourceChunk]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: ResourceChunk => resourceChunks +:= ch
      case ch => otherChunks +:= ch
    }

    (resourceChunks, otherChunks)
  }

}