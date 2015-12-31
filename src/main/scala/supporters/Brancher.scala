/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.components.StatefulComponent
import viper.silicon.Config
import viper.silicon.interfaces.{Success, Unreachable, VerificationResult}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.reporting.Bookkeeper
import viper.silicon.state.terms.{Ite, True, Not, And, Term}
import viper.silicon.state.DefaultContext
import viper.silicon.utils.Counter

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
    extends Brancher[ST, H, S, DefaultContext[H]]
       with StatefulComponent {

  private[this] type C = DefaultContext[H]

  private var branchCounter: Counter = _

  protected val decider: Decider[ST, H, PC, S, C]
  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val heapCompressor: HeapCompressor[ST, H, S, C]

  import decider.assume

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

    val exploreTrueBranch = !decider.check(σ, guardsFalse, config.checkTimeout())
    val exploreFalseBranch = !exploreTrueBranch || !decider.check(σ, guardsTrue, config.checkTimeout())

    val additionalPaths =
      if (exploreTrueBranch && exploreFalseBranch) 1
      else 0

    bookkeeper.branches += additionalPaths

    val cnt = branchCounter.next()

    /* See comment in DefaultDecider.tryOrFail */
    var originalChunks: Option[Iterable[Chunk]] = None
    def compressHeapIfRetrying(c: C, σ: S) {
      if (c.retrying) {
        originalChunks = Some(σ.h.values)
        heapCompressor.compress(σ, σ.h, c)
      }
    }
    def restoreHeapIfPreviouslyCompressed(σ: S) {
      originalChunks match {
        case Some(chunks) => σ.h.replace(chunks)
        case None => /* Nothing to do here */
      }
    }

    ((if (exploreTrueBranch) {
      val cTrue = c.copy(branchConditions = guardsTrue +: c.branchConditions)

      val result =
        decider.inScope {
          decider.prover.logComment(s"[then-branch $cnt] $guardsTrue")
          assume(guardsTrue)
          compressHeapIfRetrying(cTrue, σ)
          val r = fTrue(cTrue)
          restoreHeapIfPreviouslyCompressed(σ)
          r
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
          compressHeapIfRetrying(cFalse, σ)
          val r = fFalse(cFalse)
          restoreHeapIfPreviouslyCompressed(σ)
          r
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

  /* Lifecycle */

  abstract override def start() {
    super.start()
    branchCounter = new Counter()
  }

  abstract override def reset() {
    super.reset()
    branchCounter.reset()
  }

  abstract override def stop() = {
    super.stop()
  }
}
