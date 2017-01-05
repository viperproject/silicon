/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.interfaces._
import viper.silicon.state.State
import viper.silicon.verifier.Verifier

trait ExecutionFlowRules extends SymbolicExecutionRules {
  def locallyWithResult[R](s: State, v: Verifier)
                          (block: (State, Verifier, (R => VerificationResult)) => VerificationResult)
                          (Q: R => VerificationResult)
                          : VerificationResult

  def locally(s: State, v: Verifier)
             (block: (State, Verifier) => VerificationResult)
             : VerificationResult

  def tryOrFailWithResult[R](s: State, v: Verifier)
                            (block:    (State, Verifier, (State, R, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
                            (Q: (State, R, Verifier) => VerificationResult)
                            : VerificationResult

  def tryOrFail(s: State, v: Verifier)
               (block:    (State, Verifier, (State, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
               (Q: (State, Verifier) => VerificationResult)
               : VerificationResult
}

object executionFlowController extends ExecutionFlowRules with Immutable {
  def locallyWithResult[R](s: State, v: Verifier)
                          (block: (State, Verifier, (R => VerificationResult)) => VerificationResult)
                          (Q: R => VerificationResult)
                          : VerificationResult = {

    var optBlockData: Option[R] = None

//    println("\n[locally --- before block, before pushScope]")
//    println(s"v.uniqueId = ${v.uniqueId}")
////    println("v.decider.pcs.assumptions = ")
////    v.decider.pcs.assumptions foreach println
//    println(v.decider.pcs)

    v.decider.pushScope()

//    println("\n[locally --- before block, after pushScope]")
//    println(v.decider.pcs)

    val blockResult: VerificationResult =
      block(s, v, blockData => {
        Predef.assert(optBlockData.isEmpty,
                        "Unexpectedly found more than one block data result. Note that the local "
                      + "block is not expected to branch (non-locally)")

        optBlockData = Some(blockData)

        Success()})

//    println("\n[locally --- after block, before popScope]")
//    println(s"v.uniqueId = ${v.uniqueId}")
////    println("v.decider.pcs.assumptions = ")
////    v.decider.pcs.assumptions foreach println
//    println(v.decider.pcs)

    v.decider.popScope()

//    println("\n[locally --- after block, after popScope]")
//    println(s"v.uniqueId = ${v.uniqueId}")
////    println("v.decider.pcs.assumptions = ")
////    v.decider.pcs.assumptions foreach println
//    println(v.decider.pcs)

    blockResult match {
      case _: FatalResult =>
        /* If the local block yielded a fatal result, then the continuation Q
         * will not be invoked. That is, the current execution path will be
         * terminated.
         */
        blockResult

      case _: NonFatalResult =>
        /* If the local block yielded a non-fatal result, then the continuation
         * will only be invoked if the execution of the block yielded data
         * that the continuation Q can be invoked with, i.e. a result of type D.
         * If the block's execution did not yield such a result, then the
         * current execution path will be terminated.
         */
        optBlockData match {
          case Some(localData) => blockResult && Q(localData)
          case None => blockResult
        }
    }
  }

  def locally(s: State, v: Verifier)
             (block: (State, Verifier) => VerificationResult)
             : VerificationResult =

    locallyWithResult[VerificationResult](s, v)((s1, v1, QL) => QL(block(s1, v1)))(Predef.identity)

  def tryOrFailWithResult[R](s: State, v: Verifier)
                            (block:    (State, Verifier, (State, R, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
                            (Q: (State, R, Verifier) => VerificationResult)
                            : VerificationResult = {

    var failure: Option[Failure] = None

    var r =
      block(
        s,
        v,
        (s1, r, v1) => Q(s1, r, v1),
        f => {
          Predef.assert(failure.isEmpty, s"Expected $f to be the first failure, but already have $failure")
          failure = Some(f)
          f})

    r =
      if (failure.isEmpty)
        r
      else {
        val s0 = stateConsolidator.consolidate(s, v)
        block(s0.copy(retrying = true), v, (s1, r, v1) => Q(s1.copy(retrying = false), r, v1), f => f)
      }

//    if (failure.nonEmpty) {
//      /* TODO: The current way of having HeapCompressor change h is convenient
//       *       because it makes the compression transparent to the user, and
//       *       also, because a compression that is performed while evaluating
//       *       an expression has a lasting effect even after the evaluation,
//       *       although eval doesn't return a heap.
//       *       HOWEVER, it violates the assumption that the heap is immutable,
//       *       which is likely to cause problems, see next paragraph.
//       *       It would probably be better to have methods that potentially
//       *       compress heaps explicitly pass on a new heap.
//       *       If tryOrFail would do that, then every method using it would
//       *       have to do so as well, e.g., withChunk.
//       *       Moreover, eval might have to return a heap as well.
//       */
//      /*
//       * Restore the chunks as they existed before compressing the heap.
//       * The is done to avoid problems with the DefaultBrancher, where
//       * the effects of compressing the heap in one branch leak into the
//       * other branch.
//       * Consider the following method specs:
//       *   requires acc(x.f, k) && acc(y.f, k)
//       *   ensures x == y ? acc(x.f, 2 * k) : acc(x.f, k) && acc(y.f, k)
//       * Compressing the heap inside the if-branch updates the same h
//       * that is passed to the else-branch, which then might not verify,
//       * because now x != y but the heap only contains acc(x.f, 2 * k)
//       * (or acc(y.f, 2 * k)).
//       */
//      /* Instead of doing what's currently done, the DefaultBrancher could also
//       * be changed s.t. it resets the chunks after backtracking from the first
//       * branch. The disadvantage of that solution, however, would be that the
//       * DefaultBrancher would essentially have to clean up an operation that
//       * is conceptually unrelated.
//       */
//      s.h.replace(chunks)
//    }

    r
  }

  def tryOrFail(s: State, v: Verifier)
               (block:    (State, Verifier, (State, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
               (Q: (State, Verifier) => VerificationResult)
               : VerificationResult =

    tryOrFailWithResult[Unit](s, v)((s1, v1, QS, QF) => block(s1, v1, (s2, v2) => QS(s2, (), v2), QF))((s2, _, v2) => Q(s2, v2))
}
