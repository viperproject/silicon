/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import scala.collection.mutable
import org.slf4s.Logging
import silver.ast
import interfaces.state.{Context, Store, Heap, PathConditions, State, Chunk, StateFormatter, HeapCompressor,
    StateFactory}
import interfaces.decider.Decider
import terms.{Term, True, Implies, And, PermPlus, PermLess, PermAtMost}
import terms.perms.IsPositive
import reporting.Bookkeeper

/*
 * Immutable implementation of the necessary state interfaces
 */

/*
 * State components
 */

case class MapBackedStore(private val map: Map[ast.AbstractLocalVar, Term])
    extends Store[MapBackedStore] {

  def this() = this(Map[ast.AbstractLocalVar, Term]())
  def this(pair: (ast.AbstractLocalVar, Term)) = this(Map(pair))

  val values = map
  def empty = new MapBackedStore()
  def apply(key: ast.AbstractLocalVar) = map(key)
  def get(key: ast.AbstractLocalVar) = map.get(key)
  def +(entry: (ast.AbstractLocalVar, Term)) = MapBackedStore(map + entry)
  def +(other: MapBackedStore) = MapBackedStore(map ++ other.map)
}

case class ListBackedHeap(private var chunks: List[Chunk]) extends Heap[ListBackedHeap] {
  def this() = this(Nil)
  def this(h: ListBackedHeap) = this(h.chunks)
  def this(chunks: Iterable[Chunk]) = this(chunks.toList)

  @inline
  def values = chunks

  /** Attention: This is a destructive operation that replaces the chunks in
    * this heap by `chunks`. Only use this operation if you think that you know
    * what you are doing! Consider creating a new heap via `this(chunks)`
    * instead.
    */
  def replace(chunks: Iterable[Chunk]) {
    this.chunks = chunks.toList
  }

  def empty = new ListBackedHeap()

  def +(ch: Chunk) = ListBackedHeap(chunks :+ ch)
  def +(h: ListBackedHeap) = new ListBackedHeap(h.chunks ::: chunks)

  def -(ch: Chunk) = new ListBackedHeap(chunks.filterNot(_ == ch))
}

class MutableSetBackedPathConditions() extends PathConditions[MutableSetBackedPathConditions] {
  private val stack = mutable.Stack[Term]()
  private val set  = MSet[Term]()
  private val scopeMarker: Term = null

  def empty = new MutableSetBackedPathConditions()

  def values = toSet(set.collect{case t: Term if t != null => t})
  def contains(t: Term) = if (t == null) false else set.contains(t)

  def push(t: Term) = {
    assert(t != null, "Term must not be null.")
    stack.push(t)
    set.add(t)
    this
  }

  def pop() = {
    set.remove(stack.pop())
    this
  }

  def pushScope() = {
    stack.push(scopeMarker)
    this
  }

  def popScope() = {
    var t: Term = null

    while ({t = stack.pop(); t != null}) {
      set.remove(t)
    }

    this
  }
}

/*
 * State
 */

case class DefaultState[ST <: Store[ST], H <: Heap[H]]
                       (γ: ST,
                        h: H,
                        g: H,
                        getPathConditions: () => Set[Term])
    extends State[ST, H, DefaultState[ST, H]] {

  def \(γ: ST) = this.copy(γ = γ)
  def \+(γ: ST) = this.copy(γ = this.γ + γ)
  def \+(v: ast.AbstractLocalVar, t: Term) = this.copy(γ = this.γ + (v, t))

  def \(h: H) = this.copy(h = h)
  def \(h: H, g: H) = this.copy(h = h, g = g)
  def \+(c: Chunk) = this.copy(h = this.h + c)
  def \+(h: H) = this.copy(h = this.h + h)
  def \-(c: Chunk) = this.copy(h = this.h - c)

  def \(γ: ST = γ, h: H = h, g: H = g) = this.copy(γ, h, g)

  lazy val π = getPathConditions()
}

/*
 * Utils
 */

class DefaultHeapCompressor[ST <: Store[ST],
                            H <: Heap[H],
                             PC <: PathConditions[PC],
                            S <: State[ST, H, S],
                             C <: Context[C]]
                           (val decider: Decider[ST, H, PC, S, C],
                            val distinctnessLowerBound: Term,
                            val stateFormatter: StateFormatter[ST, H, S, String],
                            val stateFactory: StateFactory[ST, H, S],
                            val config: Config,
                            val bookkeeper: Bookkeeper)
    extends HeapCompressor[ST, H, S, C] with Logging {

  import stateFactory.H

  /** Attention: Compressing the heap modifies `h`, that is, its internal
    * representation! After compressing the heap, `h` is updated via
    * calling `h.replace(...)`.
    */
  def compress(σ: S, h: H, ctx: C) {
    var tSnaps = Set[Term]()
    var rts = Set[Term]()

    val (permissionChunks, otherChunk) = h.values.partition(_.isInstanceOf[DirectChunk])

    var rh: H = null.asInstanceOf[H]
    var h1 = H()
    var h2 = H(permissionChunks)

    /* TODO: Possible improvements
     *  - Pushing path conditions directly via prover.assume means that they are not
     *    reflected in the State, which could cause confusion while debugging.
     *  - Path conditions are prover.push'ed, then prover.pop'ped again, and then
     *    later on decider.assume'ed again.
     *
     * TODO: Don't use heaps during compression, just work on Iterable[Chunk] or Set[Chunk]
     */

    decider.pushScope()
    do {
      val result = singleMerge(σ, h1, h2, ctx)
      rh = result._1
      rts = result._4

      rts foreach decider.prover.assume

      tSnaps = tSnaps ++ rts
      h1 = H()
      h2 = rh
    } while(rts.nonEmpty)
    decider.popScope()

    assumeValidPermissionAmounts(rh)

    val tDists = deriveReferenceInequalities(σ, rh)

    decider.assume(tSnaps ++ tDists)

    h.replace(rh.values ++ otherChunk)
  }

  def merge(σ: S, h: H, ch: Chunk, ctx: C): (H, Option[DirectChunk]) = {
    val (h1, _, matches, ts) = singleMerge(σ, h, H(ch :: Nil), ctx)
    
    decider.assume(ts)
    
    val optMatch = ch match {
      case dc: DirectChunk => matches.get(dc)
      case _ => None
    } 
    
    (h1, optMatch)
  }

  /** Merges `h2` into `h1`, yielding a quadruple `(h, dfcs, matches, ts)`,
    * where `h` is the heap resulting from the merge.
    * `dfcs` are all those `DirectFieldChunk`s that have been affected by the
    * merge, i.e., that are either completely new (from `h2`) or that are the
    * result of merging a chunk from `h2` with an already existing chunk from `h1`.
    * Entries `(c1 -> c2)` in `matches` are such, that `c2` is a chunk from `h2`
    * that was merged which `c1`, where `c1` is either from `h1`, or is the
    * result of an earlier merge between a chunk from `h1` and `h2`.
    * `ts` are path conditions resulting from the merge, i.e., (conditional)
    * equalities between snapshots of merged chunks.
    *
    * @param σ Current state.
    * @param h1 Heap to merge into `h2`.
    * @param h2 Heap into which `h1` will be merged in.
    * @return Result quadruple.
    */
  private def singleMerge(σ: S, h1: H, h2: H, ctx: C)
                         : (H, List[DirectFieldChunk], Map[DirectChunk, DirectChunk], Set[Term]) = {

    bookkeeper.heapMergeIterations += 1

    val (rh, fcs, matches, tSnaps) = {
      /* rh: resulting heap, each t.f occurs only once
       * fcs: changeset of field chunks (completely new or merged chunks)
       * pi: additional path conditions
       */
      val initial = (h1, List[DirectFieldChunk](), Map[DirectChunk, DirectChunk](), Set[Term]())

      h2.values.foldLeft(initial) { case ((ah, afcs, amatches, ats), c2) =>
        /* ah: accumulating heap
         * afcs: accumulating new/modified field chunks
         * ats: accumulating path conditions
         * c2: current chunk of the new heap h2
         */
        (decider.getChunk[DirectChunk](σ, ah, c2.id, ctx), c2) match {
          case (Some(c1: DirectFieldChunk), c2: DirectFieldChunk) =>
            val (tSnap, tSnapDef) = combineSnapshots(c1.value, c2.value, c1.perm, c2.perm)
            val c3 = c1.copy(perm = PermPlus(c1.perm, c2.perm), value = tSnap)
            (ah - c1 + c3, c3 :: afcs, amatches + (c1 -> c2), ats + tSnapDef)

          case (Some(c1: DirectPredicateChunk), c2: DirectPredicateChunk) =>
            val (tSnap, tSnapDef) = combineSnapshots(c1.snap, c2.snap, c1.perm, c2.perm)
            val c3 = c1.copy(perm = PermPlus(c1.perm, c2.perm), snap = tSnap)
            (ah - c1 + c3, afcs, amatches + (c1 -> c2), ats + tSnapDef)

          case (Some(other), _) =>
            sys.error(
              s"""[DefaultHeapUtils.merge] Chunks with
                 |  id = ${c2.id}
                 |and types
                 |  c1 = ${other.getClass.getName},
                 |  c2 = ${c2.getClass.getName}
                 |were not expected to appear in heaps
                 |  h1 = ${stateFormatter.format(h1)},
                 |  h2 = ${stateFormatter.format(h2)}.""".stripMargin)

          case (None, c2: DirectFieldChunk) => (ah + c2, c2 :: afcs, amatches, ats)
          case (None, _) => (ah + c2, afcs, amatches, ats)
        }}
    }

    (rh, fcs, matches, tSnaps)
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
  private def deriveReferenceInequalities(σ: S, h: H): List[Term] = {
    bookkeeper.objectDistinctnessComputations += 1

    val pairsPerField = mutable.HashMap[String, mutable.ListBuffer[(Term, Term)]]()

    def add(fieldName: String, rcvr: Term, perm: Term) {
      pairsPerField.getOrElseUpdate(fieldName, mutable.ListBuffer[(Term, Term)]())
                   .append((rcvr, perm))
    }

    h.values foreach {
      case DirectFieldChunk(rcvr, fieldName, _, perm) =>
        add(fieldName, rcvr, perm)
      case _ =>
    }

    val tDists = mutable.ListBuffer[Term]()

    for ((fieldName, pairs) <- pairsPerField;
         Seq((rcvr1, perm1), (rcvr2, perm2)) <- pairs.combinations(2)) {

      if (   rcvr1 != rcvr2 /* Not essential for soundness, but avoids fruitless prover calls */
          && decider.check(σ, PermLess(distinctnessLowerBound, PermPlus(perm1, perm2)), config.checkTimeout())) {

        tDists += (rcvr1 !== rcvr2)
      }
    }

    tDists.result()
  }

  private def assumeValidPermissionAmounts(h: H) {
    h.values foreach {
      case fc: DirectFieldChunk => decider.assume(PermAtMost(fc.perm, distinctnessLowerBound))
      case _=>
    }
  }
}
