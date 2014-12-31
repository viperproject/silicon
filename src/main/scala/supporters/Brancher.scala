/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import interfaces.{HasLocalState, Success, Unreachable, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{PathConditions, Context, State, Heap, Store}
import reporting.Bookkeeper
import state.terms.{Ite, True, Not, And, Term}

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

  /* TODO: Remove this method, keep only the above */
  def branch(σ: S,
             ts: List[Term],
             c: C,
             fTrue: C => VerificationResult,
             fFalse: C => VerificationResult)
            : VerificationResult

  def branchAndJoin(σ: S,
                    guard: Term,
                    c: C,
                    fTrue: (C, (Term, C) => VerificationResult) => VerificationResult,
                    fFalse: (C, (Term, C) => VerificationResult) => VerificationResult)
                   (Q: (Option[Term], Option[Term], C) => VerificationResult)
                   : VerificationResult

  def guards: Stack[Term]
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

  val decider: Decider[ST, H, PC, S, C]
  import decider.assume

  val bookkeeper: Bookkeeper


  /*private*/ var currentGuards: Stack[Term] = Stack()
  def guards = this.currentGuards

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

    val guardsTrue = And(ts: _*)
    val guardsFalse = And(ts map (t => Not(t)): _*)

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

  def branchAndJoin(σ: S,
                    guard: Term,
                    c: C,
                    fTrue: (C, (Term, C) => VerificationResult) => VerificationResult,
                    fFalse: (C, (Term, C) => VerificationResult) => VerificationResult)
                   (Q: (Option[Term], Option[Term], C) => VerificationResult)
                   : VerificationResult = {

    val πPre: Set[Term] = decider.π
    var πThen: Option[Set[Term]] = None
    var tThen: Option[Term] = None
    var cThen: Option[C] = None
    var πElse: Option[Set[Term]] = None
    var tElse: Option[Term] = None
    var cElse: Option[C] = None

    val r =
      branch(σ, guard, c,
        (c1: C) =>
          fTrue(c1,
                (t, c2) => {
                  assert(πThen.isEmpty, s"Unexpected branching occurred")
                  πThen = Some(decider.π -- (πPre + guard))
                  tThen = Some(t)
                  cThen = Some(c2)
                  Success()}),
        (c1: C) =>
          fFalse(c1,
                (t, c2) => {
                  assert(πElse.isEmpty, s"Unexpected branching occurred")
                  πElse = Some(decider.π -- (πPre + guard))
                  tElse = Some(t)
                  cElse = Some(c2)
                  Success()}))

    r && {
      val tAuxIte = /* Ite with auxiliary terms */
        Ite(guard,
            πThen.fold(True(): Term)(ts => And(ts)),
            πElse.fold(True(): Term)(ts => And(ts)))

      assume(tAuxIte)

      val cJoined = (cThen, cElse) match {
        case (Some(_cThen), Some(_cElse)) => _cThen.merge(_cElse)
        case (None, Some(_cElse)) => _cElse
        case (Some(_cThen), None) => _cThen
        case (None, None) => c
      }

      Q(tThen, tElse, cJoined)
    }
  }
}
