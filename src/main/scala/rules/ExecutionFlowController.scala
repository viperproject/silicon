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

    v.decider.pushScope()

    val blockResult: VerificationResult =
      block(s, v, blockData => {
        Predef.assert(optBlockData.isEmpty,
                        "Unexpectedly found more than one block data result. Note that the local "
                      + "block is not expected to branch (non-locally)")

        optBlockData = Some(blockData)

        Success()})

    v.decider.popScope()

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

    r
  }

  def tryOrFail(s: State, v: Verifier)
               (block:    (State, Verifier, (State, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
               (Q: (State, Verifier) => VerificationResult)
               : VerificationResult =

    tryOrFailWithResult[Unit](s, v)((s1, v1, QS, QF) => block(s1, v1, (s2, v2) => QS(s2, (), v2), QF))((s2, _, v2) => Q(s2, v2))
}
