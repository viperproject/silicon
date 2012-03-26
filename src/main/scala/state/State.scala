package ch.ethz.inf.pm.silicon.state

import com.weiglewilczek.slf4s.Logging
import ch.ethz.inf.pm.silicon
import silicon.interfaces.state.{Store, Heap, PathConditions, State, Chunk, 
		StateFormatter, HeapMerger, FieldChunk, PredicateChunk}
// import silicon.interfaces.reporting.Context
import silicon.interfaces.decider.Decider
// import silicon.ast.Variable
import silicon.state.terms.{Term, PermissionTerm}
import silicon.reporting.Bookkeeper

/*
 * Immutable implementation of the necessary state interfaces
 */

/*
 * State components
 */
 
case class MapBackedStore[V](private val map: Map[V, Term])
		extends Store[V, MapBackedStore[V]] {

	def this() = this(Map[V, Term]())
	def this(pair: (V, Term)) = this(Map(pair))

	val values = map
	def empty = new MapBackedStore()
	
  def apply(key: V) = get(key).get

	def get(key: V) = {
    /* TODO: Remove hack! */
    val pa = key.asInstanceOf[silAST.programs.symbols.ProgramVariable]
    val mpa = map.asInstanceOf[Map[silAST.programs.symbols.ProgramVariable, Term]]
    mpa.get(mpa.keys.find(_.name == pa.name).get)
  }
    
	def +(entry: (V, Term)) = MapBackedStore(map + entry)
	def +(other: MapBackedStore[V]) = MapBackedStore(map ++ other.map)
}

case class MapBackedHeap(private val chunks: Map[(Term, String), Chunk])
		extends Heap[MapBackedHeap] {

	def this() = this(Map[(Term, String), Chunk]())
	def this(h: MapBackedHeap) = this(h.chunks)
	def this(chunks: Iterable[Chunk]) =
		this(chunks.map(c => ((c.rcvr, c.id) -> c)).toMap)	

	val values = chunks.values /* Incorrect if chunks is modified anywhere */
	def empty = new MapBackedHeap()

	def +(c: Chunk) = new MapBackedHeap(chunks + ((c.rcvr, c.id) -> c))
	def +(h: MapBackedHeap) = new MapBackedHeap(chunks ++ h.chunks)
	def -(c: Chunk) = new MapBackedHeap(chunks - ((c.rcvr, c.id)))
}

/* TODO: Why is this implementation mutable while all others aren't? */
class MutableSetBackedPathConditions()
		extends PathConditions[MutableSetBackedPathConditions] {

	import collection.mutable.{Stack, HashSet}

	private val stack: Stack[Term] = Stack()
	private val set: HashSet[Term] = HashSet()
	private val scopeMarker: Term = null

	def empty = new MutableSetBackedPathConditions()

	def values = set.collect{case t: Term if t != null => t}.toSet
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
		var t: Term = null;
		
		while ({t = stack.pop(); t != null}) {
			set.remove(t)
		}
		
		this
	}
}

/*
 * State
 */

case class DefaultState[V, ST <: Store[V, ST], H <: Heap[H]]
		(	val γ: ST,
			val h: H,
			val g: H,
			val getPathConditions: () => Set[Term])
		extends State[V, ST, H, DefaultState[V, ST, H]] {

	def \(γ: ST) = this.copy(γ = γ)
	def \+(γ: ST) = this.copy(γ = this.γ + γ)
	def \+(v: V, t: Term) = this.copy(γ = this.γ + (v, t))
	
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

class DefaultHeapMerger[V, ST <: Store[V, ST], H <: Heap[H],
												PC <: PathConditions[PC], S <: State[V, ST, H, S]]
		(val decider: Decider[V, ST, H, PC, S],
		 val distinctnessLowerBound: PermissionTerm,
		 val bookkeeper: Bookkeeper,
		 val stateFormatter: StateFormatter[V, ST, H, S, String])
		extends HeapMerger[H] with Logging {

	/**
	 * h1: existing heap which should NOT contain duplicated field chunks, i.e.
	 *     several chunks t1.f |-> x1 # p1, t1.f |-> x2 # p2
	 * h2: newly produced heap which can contain duplicated field chunks
	 * resulting H: merged heap where each t.f occurs only once
	 * resulting List[Term]: additional path conditions resulting from the merging
	 */
	def merge(h1in: H, h2in: H): (H, Set[Term]) = {
		var fcs: List[FieldChunk] = Nil
		var rfcs: List[FieldChunk] = Nil
		
		var tSnaps = Set[Term]()		
		var rts = Set[Term]()
		
		var rh: H = null.asInstanceOf[H]
		var h1 = h1in
		var h2 = h2in
		
		// logger.debug("$" * 20 + "  [DefaultHeapMerger.merge]  " + "$" * 20)
		// assert(!decider.checkSmoke, "SMOKE CHECK failed before heap merge\n" + decider.π)
		
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
		
		decider.prover.push()
		do {
			val result = singleMerge(h1, h2)
			rh = result._1
			rfcs = result._2
			rts = result._3
			// rts = rts.filterNot(_ == terms.True())
		
			rts foreach decider.prover.assume
			
//			if (decider.assert(terms.False())) {
//          println("Merge resulted in inconsistent state")
				// println("$" * 40)
				// println("h1 = " + h1)
				// println("h2 = " + h2)
				// println("rh = " + rh)
				// println("rts = " + rts)
				// println("$" * 40)
//			}
			
			fcs = fcs ::: rfcs
			tSnaps = tSnaps ++ rts
			h1 = h1.empty
			h2 = rh
		} while(rts.nonEmpty)
		decider.prover.pop()
		
		val tDists = deriveObjectDistinctness(rh, fcs)
				
		(rh, tSnaps ++ tDists)
	}

	private def singleMerge(h1: H, h2: H): (H, List[FieldChunk], Set[Term]) = {
		bookkeeper.heapMergeIterations += 1

		val (rh, fcs, tSnaps) = {
			/* rh: resulting heap, each t.f occurs only once
			 * fcs: changeset of field chunks (completely new or merged chunks)
			 * pi: additional path conditions
			 */
			val initial = (h1, List[FieldChunk](), Set[Term]())
			
			h2.values.foldLeft(initial) { case ((ah, afcs, ats), c2) =>
				/* ah: accumulating heap
				 * afcs: accumulating new/modified field chunks
				 * ats: accumulating path conditions
				 * c2: current chunk of the new heap h2
				 */			
				(decider.getChunk(ah, c2.rcvr, c2.id), c2) match {
					case (Some(c1: FieldChunk), c2: FieldChunk) =>
						val c3 = c1 + c2.perm
						val t1 = if (c1.value == c2.value) terms.True()
										 else c1.value ≡ c2.value
						(ah - c1 + c3, c3 :: afcs, ats + t1)
						
					case (Some(c1: PredicateChunk), c2: PredicateChunk) =>
						val c3 = c1 + c2.perm
						val tSnap = if (c1.snap == c2.snap) terms.True()
												else c1.snap ≡ c2.snap
						(ah - c1 + c3, afcs, ats + tSnap)

					case (Some(other), _) =>
						sys.error("[DefaultHeapUtils.merge] Chunks with t = %s, id = %s " +
                      "and types c1 = %s, c2 = %s were not expected to appear in " +
                      " heaps h1 = %s, h2 = %s.".format(c2.rcvr,
                                                        c2.id,
                                                        other.getClass.getName,
                                                        c2.getClass.getName,
                                                        stateFormatter.format(h1),
                                                        stateFormatter.format(h2)))

					case (None, c2: FieldChunk) => (ah + c2, c2 :: afcs, ats)
					case (None, _) => (ah + c2, afcs, ats)
				}}
		}
		// println("\ntSnaps = " + tSnaps)
		(rh, fcs, tSnaps)
	}
	
	private def deriveObjectDistinctness(h: H, fcs: List[FieldChunk]): List[Term] = {
		bookkeeper.objectDistinctnessComputations += 1
		
		/* Compute which objects must be distinct by considering field chunks and 
		 * access permissions.
		 * Rule: if t1.f |-> _ # p1 and t2.f |-> _ # p2 in h and p1 + p2 > 100
		 *       then t1 != t2
		 * We only consider the changeset fcs and compare each chunk in it to
		 * all chunks in h having the same field id.
		 */		
		val fields = h.values collect {case c: FieldChunk => c}
		val gs = fields groupBy(_.id)
		
		val tDists = fcs flatMap(c1 => gs(c1.id) map (c2 =>
			if (	 c1.rcvr != c2.rcvr /* Necessary since fcs is a subset of h */
					&& decider.isAsPermissive(c1.perm + c2.perm, distinctnessLowerBound))
				// terms.Not(terms.TermEq(c1.rcvr, c2.rcvr))
				c1.rcvr ≠ c2.rcvr
			else
				terms.True()))

		tDists
	}
}