package semper
package silicon
package state

import com.weiglewilczek.slf4s.Logging
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, StateFormatter, HeapCompressor, StateFactory}
import interfaces.reporting.{TraceView, Context}
import interfaces.decider.Decider
import ast.Variable
import terms.{Term, DefaultFractionalPermissions}
import terms.perms.IsAsPermissive
import reporting.Bookkeeper
import collection.mutable

/*
 * Immutable implementation of the necessary state interfaces
 */

/*
 * State components
 */

case class MapBackedStore(private val map: Map[Variable, Term])
		extends Store[MapBackedStore] {

	def this() = this(Map[Variable, Term]())
	def this(pair: (Variable, Term)) = this(Map(pair))

	val values = map
	def empty = new MapBackedStore()
	def apply(key: Variable) = map(key)
	def get(key: Variable) = map.get(key)
	def +(entry: (Variable, Term)) = MapBackedStore(map + entry)
	def +(other: MapBackedStore) = MapBackedStore(map ++ other.map)
}

case class SetBackedHeap(private var chunks: Set[Chunk]) extends Heap[SetBackedHeap] {
	def this() = this(Set[Chunk]())
	def this(h: SetBackedHeap) = this(h.chunks)
	def this(chunks: Iterable[Chunk]) = this(toSet(chunks))

  @inline
	def values = chunks

  /** Attention: This is a destructive operation that replaces the chunks in
    * this heap by `chunks`. Only use this operation if you think that you know
    * what you are doing! Consider creating a new heap via `this(chunks)`
    * instead.
    */
  def replace(chunks: Iterable[Chunk]) {
    this.chunks = toSet(chunks)
  }

	def empty = new SetBackedHeap()

	def +(ch: Chunk) = new SetBackedHeap(chunks + ch)
	def +(h: SetBackedHeap) = new SetBackedHeap(chunks ++ h.chunks)

	def -(ch: Chunk) = new SetBackedHeap(chunks - ch)
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
	def \+(v: Variable, t: Term) = this.copy(γ = this.γ + (v, t))

	def \(h: H) = this.copy(h = h)
	def \(h: H, g: H) = this.copy(h = h, g = g)
	def \+(c: Chunk) = this.copy(h = this.h + c)
	def \+(h: H) = this.copy(h = this.h + h)
	def \-(c: Chunk) = this.copy(h = this.h - c)

	def \(γ: ST = γ, h: H = h, g: H = g) = this.copy(γ, h, g)

	def π = getPathConditions()
}

/*
 * Utils
 */

class DefaultHeapCompressor[ST <: Store[ST],
                            H <: Heap[H],
											     	PC <: PathConditions[PC],
                            S <: State[ST, H, S],
											     	C <: Context[C, ST, H, S],
                            TV <: TraceView[TV, ST, H, S]]
                           (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV],
                            val distinctnessLowerBound: DefaultFractionalPermissions,
                            val bookkeeper: Bookkeeper,
                            val stateFormatter: StateFormatter[ST, H, S, String],
                            val stateFactory: StateFactory[ST, H, S])
		extends HeapCompressor[ST, H, S] with Logging {

  import stateFactory.H

  /** Attention: Compressing the heap modifies `h`, that is, its internal
    * representation! After compressing the heap, `h` is updated via
    * calling `h.replace(...)`.
    */
	def compress(σ: S, h: H) {
		var fcs: List[DirectFieldChunk] = Nil
		var rfcs: List[DirectFieldChunk] = Nil

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
		 *  - It might be sufficient to consider the changeset rfcs and to merge
		 *    that with the other chunks, or even iteratively into an empty chunk.
		 *    The result would finally be merged with the complete heap.
		 *    Not sure if that turns out to be sufficient, though.
		 */

    /* TODO: Don't use heaps during compression, just work on Iterable[Chunk] or Set[Chunk] */

		decider.pushScope()
		do {
			val result = singleMerge(σ, h1, h2)
			rh = result._1
			rfcs = result._2
			rts = result._3

			rts foreach decider.prover.assume

			fcs = fcs ::: rfcs
			tSnaps = tSnaps ++ rts
			h1 = H()
			h2 = rh
		} while(rts.nonEmpty)
		decider.popScope()

		val tDists = deriveObjectDistinctness(σ, rh, fcs)

    decider.assume(tSnaps ++ tDists)

    h.replace(rh.values ++ otherChunk)
	}

	private def singleMerge(σ: S, h1: H, h2: H): (H, List[DirectFieldChunk], Set[Term]) = {
		bookkeeper.heapMergeIterations += 1

		val (rh, fcs, tSnaps) = {
			/* rh: resulting heap, each t.f occurs only once
			 * fcs: changeset of field chunks (completely new or merged chunks)
			 * pi: additional path conditions
			 */
			val initial = (h1, List[DirectFieldChunk](), Set[Term]())

			h2.values.foldLeft(initial) { case ((ah, afcs, ats), c2) =>
				/* ah: accumulating heap
				 * afcs: accumulating new/modified field chunks
				 * ats: accumulating path conditions
				 * c2: current chunk of the new heap h2
				 */
				(decider.getChunk[Chunk](σ, ah, c2.id), c2) match {
					case (Some(c1: DirectFieldChunk), c2: DirectFieldChunk) =>
						val c3 = c1 + c2.perm
						val t1 = if (c1.value == c2.value) terms.True()
										 else c1.value === c2.value
						(ah - c1 + c3, c3 :: afcs, ats + t1)

					case (Some(c1: DirectPredicateChunk), c2: DirectPredicateChunk) =>
						val c3 = c1 + c2.perm
						val tSnap = if (c1.snap == c2.snap) terms.True()
												else c1.snap === c2.snap
						(ah - c1 + c3, afcs, ats + tSnap)

					case (Some(other), _) =>
            sys.error("[DefaultHeapUtils.merge] Chunks with id = %s and types c1 = %s, c2 = %s were not expected to appear in heaps h1 = %s, h2 = %s.".format(c2.id, other.getClass.getName, c2.getClass.getName, stateFormatter.format(h1), stateFormatter.format(h2)))

					case (None, c2: DirectFieldChunk) => (ah + c2, c2 :: afcs, ats)
					case (None, _) => (ah + c2, afcs, ats)
				}}
		}

		(rh, fcs, tSnaps)
	}

	private def deriveObjectDistinctness(σ: S, h: H, fcs: List[DirectFieldChunk]): List[Term] = {
		bookkeeper.objectDistinctnessComputations += 1

		/* Compute which objects must be distinct by considering field chunks and
		 * access permissions.
		 * Rule: if t1.f |-> _ # p1 and t2.f |-> _ # p2 in h and p1 + p2 > 100
		 *       then t1 != t2
		 * We only consider the changeset fcs and compare each chunk in it to
		 * all chunks in h having the same field id.
		 */
		val fields = h.values collect {case c: DirectFieldChunk => c}
		val gs = fields groupBy(_.name)

		val tDists = fcs flatMap(c1 => gs(c1.name) map (c2 =>
			if (   c1.rcvr != c2.rcvr /* Necessary since fcs is a subset of h */
          && !decider.check(σ, IsAsPermissive(distinctnessLowerBound, c1.perm + c2.perm)))

				c1.rcvr !== c2.rcvr
			else
				terms.True()))

		tDists
	}
}

object SnapshotHelper {
  import terms._

  def discoverEqualities(ts: Set[Term]): Set[Term] = {
//    println("\n[discoverEqualities]")
    val eqs: MSet[Term] = MSet() ++ ts collect {case eq: Eq if eq.p0.sort == sorts.Snap => eq}
//    println(s"  eqs = $eqs")

    val newEqs = MSet[Term]()
    val discoveredEqs = MSet[Term]()
    var continue = true

    while (continue) {
      eqs foreach {
        case Eq(Combine(t0, t1), Combine(t2, t3), _) =>
          newEqs ++= List(t0 === t2, t1 === t3)
        case _ =>
      }

//      println(s"\n  newEqs|1 = $newEqs")

//      println("  [transitive closure loop]")
      for(Eq(t0, t1, _) <- eqs; Eq(t2, t3, _) <- eqs) {
//        println(s"    ($t0, $t1) ? ($t2, $t3)")
        if (t0 == t2 && t1 != t3) newEqs += t1 === t3
        if (t0 == t3 && t1 != t2) newEqs += t1 === t2
        if (t1 == t2 && t0 != t3) newEqs += t0 === t3
        if (t1 == t3 && t0 != t2) newEqs += t0 === t2
      }

      newEqs --= eqs

      continue = newEqs.nonEmpty
      eqs ++= newEqs
      discoveredEqs ++= newEqs

//      println(s"  newEqs|2 = $newEqs")

      newEqs.clear()
    }

//    println(s"  discoveredEqs = $discoveredEqs")

    toSet(discoveredEqs)
  }
}
