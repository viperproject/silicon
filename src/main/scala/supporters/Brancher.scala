/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import interfaces.{Success, Unreachable, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{PathConditions, Context, State, Heap, Store}
import reporting.Bookkeeper
import state.terms.{Ite, True, Not, And, Term}
import viper.silicon.state.DefaultContext

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
}

/*
 * Implementations
 */

trait DefaultBrancher[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    extends Brancher[ST, H, S, DefaultContext[H]] {

  private[this] type C = DefaultContext[H]

  val decider: Decider[ST, H, PC, S, C]
  import decider.assume

  val bookkeeper: Bookkeeper

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
      val cTrue = c.copy(branchConditions = guardsTrue +: c.branchConditions)

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          fTrue(cTrue)
        }

      result
    } else {
      decider.prover.logComment(s"[dead then-branch $cnt] $guardsTrue")
      Unreachable()
    })
      &&
    (if (exploreFalseBranch) {
      val cFalse = c.copy(branchConditions = guardsFalse +: c.branchConditions)

      val result =
        decider.inScope {
          decider.prover.logComment(s"[else-branch $cnt] $guardsFalse")
          assume(guardsFalse)
          fFalse(cFalse)
        }

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
        case (Some(_cThen), Some(_cElse)) =>
          val cThen0 = _cThen.copy(branchConditions = c.branchConditions)
          val cElse0 = _cElse.copy(branchConditions = c.branchConditions)
          /* TODO: Modifying the branchConditions before merging contexts is only necessary
           *       because DefaultContext.merge (correctly) insists on equal branchConditions,
           *       which cannot be circumvented/special-cased when merging contexts here.
           *       See DefaultJoiner.join for a similar comment.
           */
          cThen0.merge(cElse0)
        case (None, Some(_cElse)) => _cElse
        case (Some(_cThen), None) => _cThen
        case (None, None) => c
      }

      Q(tThen, tElse, cJoined.copy(branchConditions = c.branchConditions))
    }
  }
}
