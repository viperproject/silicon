package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.{InsufficientPermission}
import interfaces.{VerificationResult, Failure, Unreachable}
import interfaces.decider.Decider
import interfaces.reporting.{Context, TraceView, TwinBranchingStep, LocalTwinBranchingStep,
    TwinBranch, LocalTwinBranch, Step}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, StateFormatter, PermissionChunk}
import state.terms._
import state.terms.utils.{BigAnd, ¬}
import state.DirectChunk
import reporting.Bookkeeper
import utils.notNothing._

/* TODO: Move interfaces into interfaces package */

trait HasLocalState {
	def pushLocalState() {}
	def popLocalState() {}
}

trait Brancher[ST <: Store[ST],
               H <: Heap[H],
               S <: State[ST, H, S],
               C <: Context[C, ST, H, S],
               TV <: TraceView[TV, ST, H, S]] {

  def branchLocally(ts: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult

	def branch(ts: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult

	def branch(ts: List[Term],
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult
}

//trait ARPSupporter[ST <: Store[ST],
//                   H <: Heap[H],
//                   S <: State[ST, H, S],
//                   C <: Context[C, ST, H, S] {
//
//  def con(id: String, upperBound: FractionalPermissions, c: C)
//}

/*
 * Implementations
 */

trait DefaultBrancher[ST <: Store[ST],
                      H <: Heap[H],
							        PC <: PathConditions[PC],
                      S <: State[ST, H, S],
							        C <: Context[C, ST, H, S],
                      TV <: TraceView[TV, ST, H, S]]
		extends Brancher[ST, H, S, C, TV] with HasLocalState {

	val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
	import decider.assume

	val bookkeeper: Bookkeeper

  def branchLocally(t: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUpLocally(c, stepFactory)

    branch(t :: Nil, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
	}

	def branch(t: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult =

    branch(t :: Nil, c, tv, stepFactory, fTrue, fFalse)

  def branch(ts: List[Term],
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
             fFalse: (C, TV) => VerificationResult)
            : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUp(c, stepFactory)

    branch(ts, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
  }

	private def branch(ts: List[Term],
                     cTrue: C,
                     cFalse: C,
                     tvTrue: TV,
                     tvFalse: TV,
                     fTrue: (C, TV) => VerificationResult,
						         fFalse: (C, TV) => VerificationResult)
                    : VerificationResult = {

		val guardsTrue = BigAnd(ts)
		val guardsFalse = BigAnd(ts, t => ¬(t))

		val exploreTrueBranch = !decider.assert(guardsFalse)
    val exploreFalseBranch = !decider.assert(guardsTrue)

		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		bookkeeper.branches += additionalPaths


		((if (exploreTrueBranch) {
			pushLocalState()
      val result =
        decider.inScope {
          assume(guardsTrue, cTrue)
          fTrue(cTrue, tvTrue)
        }
      popLocalState()
			result
		} else Unreachable[C, ST, H, S](cTrue))
			&&
		(if (exploreFalseBranch) {
			pushLocalState()
      val result =
        decider.inScope {
          assume(guardsFalse, cFalse)
          fFalse(cFalse, tvFalse)
        }
      popLocalState()
			result
		} else Unreachable[C, ST, H, S](cFalse)))
	}
}

trait ChunkFinder[P <: FractionalPermissions[P],
                  ST <: Store[ST],
                  H <: Heap[H],
                  S <: State[ST, H, S],
                  C <: Context[C, ST, H, S],
                  TV <: TraceView[TV, ST, H, S]] {

	def withChunk[CH <: Chunk : NotNothing : Manifest]
               (h: H,
                rcvr: Term,
                id: String,
                memloc: ast.MemoryLocation,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
							 (Q: CH => VerificationResult)
               : VerificationResult

  /* TODO: Should be CH <: PermissionChunk[P, CH], but I couldn't get the compiler to accept the implementation
   *       provided by DefaultChunkFinder.withChunk.
   */
  def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (h: H,
                rcvr: Term,
                id: String,
                p: P,
                memloc: ast.MemoryLocation,
                ve: PartialVerificationError,
                c: C,
                tv: TV)
               (Q: CH => VerificationResult)
               : VerificationResult
}

class DefaultChunkFinder[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S],
                         C <: Context[C, ST, H, S],
                         TV <: TraceView[TV, ST, H, S]]
                        (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C],
                         val stateFormatter: StateFormatter[ST, H, S, String])
		extends ChunkFinder[DefaultFractionalPermissions, ST, H, S, C, TV] with Logging {

	def withChunk[CH <: Chunk : NotNothing : Manifest]
               (h: H,
                rcvr: Term,
                id: String,
                memloc: ast.MemoryLocation,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
							 (Q: CH => VerificationResult)
               : VerificationResult = {

		decider.getChunk[CH](h, rcvr, id) match {
			case Some(c) /* if manifest[CH].erasure.isInstance(c) */ =>
        Q(c)

			case None =>
//				val loc = if (m.loc != ast.NoLocation) m.loc else rcvrSrc.sourceLocation

//				if (decider.checkSmoke)	{
//					logger.debug("%s: Detected inconsistent state looking up a chunk for %s.%s.".format(loc, e, id))
//					logger.debug("π = " + stateFormatter.format(decider.π))
//
//					// val warning = Warning(SmokeDetectedAtChunkLookup at pos withDetails(e, id), c)
//					// warning
//					Success[C, ST, H, S](c)
//				} else
//					Failure[C, ST, H, S, TV](m at loc dueTo InsufficientPermissions(rcvrSrc.toString, id), c, tv)
          /* TODO: We need the location node, not only the receiver. */
					Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(memloc), c, tv)
		}
	}

	def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (h: H,
                rcvr: Term,
                id: String,
                p: DefaultFractionalPermissions,
                memloc: ast.MemoryLocation,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
               (Q: CH => VerificationResult)
               : VerificationResult =

		withChunk[CH](h, rcvr, id, memloc, pve, c, tv)(chunk => {
			if (decider.isAsPermissive(chunk.perm, p))
				Q(chunk)
			else
				Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(memloc), c, tv)})
}

class StateUtils[ST <: Store[ST],
                 H <: Heap[H],
                 PC <: PathConditions[PC],
                 S <: State[ST, H, S],
                 C <: Context[C, ST, H, S]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) {

//  def freshPermVar(id: String = "$p", upperBound: FractionalPermissions = FullPerm())
//                  : (Var, Term) = {
//
//    val permVar = decider.fresh(id, sorts.Perm)
//    val permVarConstraints = IsValidPerm(permVar, upperBound)
//
//    (permVar, permVarConstraints)
//  }

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPerm(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
