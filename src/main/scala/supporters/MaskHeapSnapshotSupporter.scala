// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters

import scala.collection.immutable
import viper.silver.ast
import viper.silver.ast.Field
import viper.silicon.rules.{magicWandSupporter, maskHeapSupporter}
import viper.silicon.state.{Heap, State, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.state.terms.sorts.{HeapSort, PredHeapSort, WandHeapSort}
import viper.silicon.verifier.Verifier

/** Snapshot format of the maskHeap encoding: while consuming, snapshots are per-resource
  * masks describing the consumed footprint (MaskMapTerm); a completed consume packs them
  * into a snap tree of heap-restricted-to-mask leaves (HeapToSnap). While producing,
  * snapshots are per-resource heaps (HeapMapTerm) from which values are looked up. */
class MaskHeapSnapshotSupporter(symbolConverter: SymbolConverter)
    extends DefaultSnapshotSupporter(symbolConverter) {

  override def unitSnapshot: Term = MaskMapTerm(immutable.ListMap[Any, Term]())

  private def toMaskMap(snap: Term, as: Seq[ast.Exp], s: State, v: Verifier): immutable.ListMap[Any, Term] =
    snap match {
      case mht: MaskMapTerm => mht.masks
      case hts: HeapToSnap => immutable.ListMap(hts.r -> hts.mask)
      case snp => maskHeapSupporter.convertFromSnapshot(snp, maskHeapSupporter.getResourceSeq(as, s.program), s, v)
    }

  override def combineSnapshots(s: State, snap1: Term, snap2: Term, a1: ast.Exp, a2: Seq[ast.Exp], v: Verifier): Term = {
    val fst = toMaskMap(snap1, Seq(a1), s, v)
    val snd = toMaskMap(snap2, a2, s, v)
    MaskMapTerm(maskHeapSupporter.mergePreservingFirstOrder(fst, snd))
  }

  override def finalizeConsumedSnapshot(s: State, h: Heap, snap: Term, as: Seq[ast.Exp], v: Verifier): Term = {
    val resources = maskHeapSupporter.getResourceSeq(as, s.program)
    val zeroMap: immutable.ListMap[Any, Term] =
      immutable.ListMap.from(resources.map(r => (r, if (r.isInstanceOf[ast.Field]) ZeroMask else PredZeroMask): (Any, Term)))
    val masks = toMaskMap(snap, as, s, v)
    val newMap = maskHeapSupporter.mergePreservingFirstOrder(zeroMap, masks)
    val hEval = magicWandSupporter.getEvalHeap(if (s.exhaleExt) s else s.copy(h = h), v)
    maskHeapSupporter.convertToSnapshot(newMap, resources, hEval, s, v.decider)
  }

  override def emptySnapshotConstraint(snap: => Term): Option[Term] = None

  override def adaptProduceSnapshotFunction(s: State,
                                            sf: (Sort, Verifier) => Term,
                                            as: Seq[ast.Exp],
                                            v: Verifier)
                                           : (Sort, Verifier) => Term = {
    val givenSnap = sf(sorts.Snap, v)
    val fakeTerm = if (!givenSnap.isInstanceOf[HeapMapTerm]) {
      val resources = maskHeapSupporter.getResourceSeq(as, s.program)
      val snapParts = fromSnapTree(givenSnap, resources.size)
      val heapParts = snapParts.zip(resources).map(tpl => (tpl._2,
        v.decider.createAlias(SnapToHeap(tpl._1, tpl._2, tpl._2 match {
          case field: Field => HeapSort(v.symbolConverter.toSort(field.typ))
          case _: viper.silicon.state.MagicWandIdentifier => WandHeapSort
          case _ => PredHeapSort
        }), s)))
      HeapMapTerm(immutable.ListMap.from(heapParts))
    } else {
      givenSnap
    }

    (_: Sort, _: Verifier) => fakeTerm
  }

  /* The maskHeap encoding does not split snapshots per conjunct: all conjuncts are
   * produced from the same per-resource heap map. */
  override def createSnapshotPair(s: State,
                                  sf: (Sort, Verifier) => Term,
                                  a0: ast.Exp,
                                  a1: ast.Exp,
                                  v: Verifier)
                                 : ((Sort, Verifier) => Term, (Sort, Verifier) => Term) =
    (sf, sf)
}
