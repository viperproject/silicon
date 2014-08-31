/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import interfaces.{VerificationResult, Unreachable}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, Context}
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
               C <: Context[C]] {

	def branch(σ: S,
             ts: Term,
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
            : VerificationResult

	def branch(σ: S,
             ts: List[Term],
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
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
							        C <: Context[C]]
		extends Brancher[ST, H, S, C] with HasLocalState {

	val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
	import decider.assume

	val bookkeeper: Bookkeeper


  /*private*/ var currentGuards: Stack[Term] = Stack()
  /* TODO: Use a set that preserves insertion order, should be faster than
   *       calling Stack.distinct over and over again.
   */
  def guards = this.currentGuards.distinct

	def branch(σ: S,
             t: Term,
             c: C,
             fTrue: C => VerificationResult,
						 fFalse: C => VerificationResult)
            : VerificationResult =

    branch(σ, t :: Nil, c, fTrue, fFalse)

  def branch(σ: S,
             ts: List[Term],
             c: C,
             fTrue: C => VerificationResult,
             fFalse: C => VerificationResult)
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
      currentGuards = guardsTrue +: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(c)
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
      currentGuards = guardsFalse +: currentGuards

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(c)
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
                 C <: Context[C]]
                (val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]) {

  def freshARP(id: String = "$k", upperBound: DefaultFractionalPermissions = FullPerm())
              : (Var, Term) = {

    val permVar = decider.fresh(id, sorts.Perm)
    val permVarConstraints = IsReadPermVar(permVar, upperBound)

    (permVar, permVarConstraints)
  }
}
