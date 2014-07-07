/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon

import semper.silicon.interfaces.{VerificationResult, Unreachable}
import interfaces.decider.Decider
import interfaces.reporting.{Context, TraceView, TwinBranchingStep, LocalTwinBranchingStep,
    TwinBranch, LocalTwinBranch, Step}
import interfaces.state.{Store, Heap, PathConditions, State}
import state.terms._
import state.terms.utils.{BigAnd, ¬}
import reporting.Bookkeeper

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

  def branchLocally(σ: S,
                    ts: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult

	def branch(σ: S,
             ts: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult

	def branch(σ: S,
             ts: List[Term],
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

	val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]
	import decider.assume

	val bookkeeper: Bookkeeper


  /*private*/ var currentGuards: Stack[Term] = Stack()
  /* TODO: Use a set that preserves insertion order, should be faster than
   *       calling Stack.distinct over and over again.
   */
  def guards = this.currentGuards.distinct

  def branchLocally(σ: S,
                    t: Term,
                    c: C,
                    tv: TV,
                    stepFactory:    (Boolean, LocalTwinBranch[ST, H, S], Step[ST, H, S])
                                 => LocalTwinBranchingStep[ST, H, S],
                    fTrue: (C, TV) => VerificationResult,
                    fFalse: (C, TV) => VerificationResult)
                   : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUpLocally(c, stepFactory)

    branch(σ, t :: Nil, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
	}

	def branch(σ: S,
             t: Term,
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
						 fFalse: (C, TV) => VerificationResult)
            : VerificationResult =

    branch(σ, t :: Nil, c, tv, stepFactory, fTrue, fFalse)

  def branch(σ: S,
             ts: List[Term],
             c: C,
             tv: TV,
             stepFactory:    (Boolean, TwinBranch[ST, H, S], Step[ST, H, S])
                          => TwinBranchingStep[ST, H, S],
             fTrue: (C, TV) => VerificationResult,
             fFalse: (C, TV) => VerificationResult)
            : VerificationResult = {

    val (cTrue, cFalse, tvTrue, tvFalse) = tv.splitUp(c, stepFactory)

    branch(σ, ts, cTrue, cFalse, tvTrue, tvFalse, fTrue, fFalse)
  }

	private def branch(σ: S,
                     ts: List[Term],
                     cTrue: C,
                     cFalse: C,
                     tvTrue: TV,
                     tvFalse: TV,
                     fTrue: (C, TV) => VerificationResult,
						         fFalse: (C, TV) => VerificationResult)
                    : VerificationResult = {

		val guardsTrue = BigAnd(ts)
		val guardsFalse = BigAnd(ts, t => ¬(t))

    val exploreTrueBranch = !decider.check(σ, guardsFalse)
    val exploreFalseBranch = !decider.check(σ, guardsTrue)

		val additionalPaths =
			if (exploreTrueBranch && exploreFalseBranch) 1
			else 0

		bookkeeper.branches += additionalPaths

    val cnt = utils.counter.next()

		((if (exploreTrueBranch) {
			pushLocalState()
      currentGuards = guardsTrue :: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(cTrue, tvTrue)
        }

      currentGuards = currentGuards.tail
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead then-branch $cnt] $guardsTrue")
      Unreachable()
    })
			&&
		(if (exploreFalseBranch) {
			pushLocalState()
      currentGuards = guardsFalse :: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(cFalse, tvFalse)
        }

      currentGuards = currentGuards.tail
      popLocalState()

			result
		} else {
      decider.prover.logComment(s"[dead else-branch $cnt] $guardsFalse")
      Unreachable()
    }))
	}
}

class StateUtils[ST <: Store[ST],
                 H <: Heap[H],
                 PC <: PathConditions[PC],
                 S <: State[ST, H, S],
                 C <: Context[C, ST, H, S],
                 TV <: TraceView[TV, ST, H, S]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C, TV]) {

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
