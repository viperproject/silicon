package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.verifier.reasons.InsufficientPermission
import semper.silicon.interfaces.{Success, VerificationResult, Failure, Unreachable}
import interfaces.decider.Decider
import interfaces.reporting.{Context, TraceView, TwinBranchingStep, LocalTwinBranchingStep,
    TwinBranch, LocalTwinBranch, Step}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, StateFormatter, ChunkIdentifier}
import state.terms._
import state.terms.utils.{BigAnd, ¬}
import state.DirectChunk
import reporting.Bookkeeper
import silicon.utils.notNothing._

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

  def guards: Seq[Term]
}

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


  private var currentGuards: Stack[Term] = Stack()

  def guards = this.currentGuards

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

    decider.prover.logComment("trololo " + ts)

		val guardsTrue = BigAnd(ts)
		val guardsFalse = BigAnd(ts, t => ¬(t))

    decider.prover.logComment("guards true " + guardsTrue)
    decider.prover.logComment("guards false " + guardsFalse)

    decider.prover.logComment("explore true branch:")
		val exploreTrueBranch = !decider.assert(guardsFalse)
    decider.prover.logComment("explore false branch:")
    val exploreFalseBranch = !decider.assert(guardsTrue)

    decider.prover.logComment("exploring true: " + exploreTrueBranch + " exploring false: " + exploreFalseBranch)

		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		bookkeeper.branches += additionalPaths

    val cnt = utils.counter.next()

		((if (exploreTrueBranch) {
			pushLocalState()
      currentGuards = currentGuards.push(guardsTrue)

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(cTrue, tvTrue)
        }

      currentGuards = currentGuards.pop
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead then-branch $cnt] $guardsTrue")
      Unreachable[C, ST, H, S](cTrue)
    })
			&&
		(if (exploreFalseBranch) {
			pushLocalState()
      currentGuards = currentGuards.push(guardsFalse)

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(cFalse, tvFalse)
        }

      currentGuards = currentGuards.pop
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead else-branch $cnt] $guardsFalse")
      Unreachable[C, ST, H, S](cFalse)
    }))
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
                id: ChunkIdentifier,
                locacc: ast.LocationAccess,
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
                id: ChunkIdentifier,
                p: P,
                locacc: ast.LocationAccess,
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

	/**
	 * Lets the decider lookup the chunk in the given heap
	 * fails if there is none
	 */
	def withChunk[CH <: Chunk : NotNothing : Manifest]
               (h: H,
                id: ChunkIdentifier,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
							 (Q: CH => VerificationResult)
               : VerificationResult = {
	  
		decider.getChunk[CH](h, id) match {
			case Some(c1) =>
        Q(c1)

			case None =>
        if (decider.assert(False()))
          Success[C, ST, H, S](c) /* TODO: Mark branch as dead? */
        else
          /* TODO: We need the location node, not only the receiver. */
          Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)
		}
	}

	/**
	 * Additionally checks if the chunk is permissive enough (e.g. for a write)
	 */
	def withChunk[CH <: DirectChunk : NotNothing : Manifest]
               (h: H,
                id: ChunkIdentifier,
                p: DefaultFractionalPermissions,
                locacc: ast.LocationAccess,
                pve: PartialVerificationError,
                c: C,
                tv: TV)
               (Q: CH => VerificationResult)
               : VerificationResult =
		withChunk[CH](h, id, locacc, pve, c, tv)(chunk => {
			if (decider.isAsPermissive(chunk.perm, p))
				Q(chunk)
			else
        if (decider.assert(False()))
          Success[C, ST, H, S](c) /* TODO: Mark branch as dead? */
			  else
          Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c, tv)})
}

class StateUtils[ST <: Store[ST],
                 H <: Heap[H],
                 PC <: PathConditions[PC],
                 S <: State[ST, H, S],
                 C <: Context[C, ST, H, S]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) {

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
