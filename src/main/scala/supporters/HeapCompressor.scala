/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import scala.collection.mutable
import org.slf4s.Logging
import viper.silicon._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.reporting.Bookkeeper
import viper.silicon.state.terms.perms._
import viper.silicon.state.{QuantifiedChunk, FieldChunk, BasicChunk}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.qps.QuantifiedChunkSupporter

trait HeapCompressor[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S], C <: Context[C]] {
  def compress(σ: S, h: H, c: C)
  def merge(σ: S, h: H, ch: PermissionChunk, c: C): (H, Option[PermissionChunk])
  def merge(σ: S, h: H, newH: H, c: C): H
}

trait HeapCompressorProvider[ST <: Store[ST],
                             H <: Heap[H],
                             S <: State[ST, H, S],
                             C <: Context[C]]
    { this: Logging =>

  protected val decider: Decider[ST, H, S, C]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val chunkSupporter: ChunkSupporter[ST, H, S, C]
  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, S, C]

  import stateFactory.H

  object heapCompressor extends HeapCompressor[ST, H, S, C] {
    /** Attention: Compressing the heap modifies `h`, that is, its internal
      * representation! After compressing the heap, `h` is updated via
      * calling `h.replace(...)`.
      */
    def compress(σ: S, h: H, c: C) {
      val (permissionChunks, otherChunk) = partition(h)

      var continue = false

      var mergedChunks: Seq[PermissionChunk] = Nil
      var destChunks: Seq[PermissionChunk] = Nil
      var newChunks: Seq[PermissionChunk] = permissionChunks

      do {
        val (_mergedChunks, _, snapEqs) = singleMerge(σ, destChunks, newChunks, c)

        snapEqs foreach decider.assume

        mergedChunks = _mergedChunks
        destChunks = Nil
        newChunks = mergedChunks
        continue = snapEqs.nonEmpty
      } while(continue)

      assumeValidPermissionAmounts(mergedChunks)

      val referenceIneqs = deriveReferenceInequalities(σ, mergedChunks)

      decider.assume(referenceIneqs)

      h.replace(mergedChunks ++ otherChunk)
    }

    def merge(σ: S, h: H, ch: PermissionChunk, c: C): (H, Option[PermissionChunk]) = {
      val (permissionChunks, otherChunk) = partition(h)
      val (mergedChunks, matches, snapEqs) = singleMerge(σ, permissionChunks, ch :: Nil, c)

      decider.assume(snapEqs)

      val optMatch = ch match {
        case ch: PermissionChunk => matches.get(ch)
        case _ => None
      }

      (H(mergedChunks ++ otherChunk), optMatch)
    }

    def merge(σ: S, h: H, newH: H, c: C): H = {
      val (permissionChunks, otherChunk) = partition(h)
      val (newPermissionChunks, newOtherChunk) = partition(newH)
      val (mergedChunks, _, snapEqs) = singleMerge(σ, permissionChunks, newPermissionChunks, c)

      decider.assume(snapEqs)

      H(mergedChunks ++ otherChunk ++ newOtherChunk)
    }

    private def singleMerge(σ: S, destChunks: Seq[PermissionChunk], newChunks: Seq[PermissionChunk], c: C)
                           : (Seq[PermissionChunk], Map[PermissionChunk, PermissionChunk], Set[Term]) = {

      bookkeeper.heapMergeIterations += 1

      /* TODO: Fix `matches` map - subsequent matches override previous matches! */

      val (mergedChunks, matches, tSnaps) = {
        val initial = (destChunks, Map[PermissionChunk, PermissionChunk](), Set[Term]())

        newChunks.foldLeft(initial) { case ((accMergedChunks, accMatches, accSnapEqs), newChunk) =>
          /* accMergedChunks: already merged chunks
           * accMatches: records
           * accSnapEqs: collected snapshot equalities
           * newChunk: current chunk from the sequence of new chunks/of chunks to merge into the
           *           sequence of destination chunks
           */

          newChunk match {
            case ch2: BasicChunk =>
              chunkSupporter.getChunk(σ, accMergedChunks, ch2.name, ch2.args, c) match {
                case Some(ch1: BasicChunk) if ch1.getClass == ch2.getClass =>
                  val (tSnap, tSnapEq) = combineSnapshots(ch1.snap, ch2.snap, ch1.perm, ch2.perm)
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

            case ch2: QuantifiedChunk =>
              (ch2 +: accMergedChunks, accMatches, accSnapEqs)
          }
        }
      }

      (mergedChunks, matches, tSnaps)
    }

    private def combineSnapshots(t1: Term, t2: Term, p1: Term, p2: Term): (Term, Term) = {
      val (tSnap, tSnapDef) =
        (IsPositive(p1), IsPositive(p2)) match {
          case (True(), b2) => (t1, Implies(b2, t1 === t2))
          case (b1, True()) => (t2, Implies(b1, t2 === t1))
          case (b1, b2) =>
            val t3 = decider.fresh(t1.sort)
            (t3,  And(Implies(b1, t3 === t1), Implies(b2, t3 === t2)))
        }

      (tSnap, tSnapDef)
    }

    /* Derives which references cannot be aliases from the available permissions */
    private def deriveReferenceInequalities(σ: S, chs: Seq[PermissionChunk]): List[Term] = {
      bookkeeper.objectDistinctnessComputations += 1

      val pairsPerField = mutable.HashMap[String, mutable.ListBuffer[(Term, Term)]]()

      def add(fieldName: String, rcvr: Term, perm: Term) {
        pairsPerField.getOrElseUpdate(fieldName, mutable.ListBuffer[(Term, Term)]())
                     .append((rcvr, perm))
      }

      chs foreach {
        case FieldChunk(rcvr, fieldName, _, perm) =>
          add(fieldName, rcvr, perm)
        case QuantifiedChunk(fieldName, _, perm, _, _, Some(rcvr), _) =>
          add(fieldName, rcvr, perm.replace(`?r`, rcvr))
        case _ =>
      }

      val tDists = mutable.ListBuffer[Term]()

      for ((_, pairs) <- pairsPerField;
           Seq((rcvr1, perm1), (rcvr2, perm2)) <- pairs.combinations(2)) {

        if (   rcvr1 != rcvr2 /* Not essential for soundness, but avoids fruitless prover calls */
            && decider.check(σ, PermLess(FullPerm(), PermPlus(perm1, perm2)), config.checkTimeout())) {

          tDists += (rcvr1 !== rcvr2)
        }
      }

      tDists.result()
    }

    private def assumeValidPermissionAmounts(chs: Seq[PermissionChunk]) {
      chs foreach {
        case fc: FieldChunk => decider.assume(PermAtMost(fc.perm, FullPerm()))
        case _=>
      }
    }

    @inline
    final private def partition(h: H): (Seq[PermissionChunk], Seq[Chunk]) = {
      var permissionChunks = Seq[PermissionChunk]()
      var otherChunks = Seq[Chunk]()

      h.values foreach {
        case ch: PermissionChunk => permissionChunks +:= ch
        case ch => otherChunks +:= ch
      }

      (permissionChunks, otherChunks)
    }
  }
}
