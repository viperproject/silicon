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

//  def tryOrFailWithResult[R](s: State, v: Verifier)
//                            (block:    (State, Verifier, (State, R, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
//                            (Q: (State, R, Verifier) => VerificationResult)
//                            : VerificationResult
//
//  def tryOrFail(s: State, v: Verifier)
//               (block:    (State, Verifier, (State, Verifier) => VerificationResult, Failure => VerificationResult) => VerificationResult)
//               (Q: (State, Verifier) => VerificationResult)
//               : VerificationResult
  def tryOrFail0(s: State, v: Verifier)
                (action: (State, Verifier, (State, Verifier) => VerificationResult) => VerificationResult)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult

  def tryOrFail1[R1](s: State, v: Verifier)
                    (action: (State, Verifier, (State, R1, Verifier) => VerificationResult) => VerificationResult)
                    (Q: (State, R1, Verifier) => VerificationResult)
                    : VerificationResult

  def tryOrFail2[R1, R2](s: State, v: Verifier)
                        (action: (State, Verifier, (State, R1, R2, Verifier) => VerificationResult) => VerificationResult)
                        (Q: (State, R1, R2, Verifier) => VerificationResult)
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


  private def tryOrFailWithResult[R](s: State, v: Verifier)
                                    (action: (State, Verifier, (State, R, Verifier) => VerificationResult) => VerificationResult)
                                    (Q: (State, R, Verifier) => VerificationResult)
                                    : VerificationResult = {

    var localActionSuccess = false
    var compressed = false

    /* TODO: Consider how to handle situations where the action branches and the first branch
     *       succeeds, i.e. localActionSuccess has been set to true, but the second fails.
     *       Currently, the verification will fail without attempting to remedy the situation,
     *       e.g. by performing a state consolidation.
     */

    val firstActionResult =
      action(
        s,
        v,
        (s1, r, v1) => {
          localActionSuccess = true
          Q(s1, r, v1)})

    val finalActionResult =
      if (   localActionSuccess /* Action succeeded locally */
          || !firstActionResult.isFatal) /* Action yielded non-fatal result (e.g. because the
                                          * current branch turned out to be infeasible) */
        firstActionResult
      else {
        val s0 = stateConsolidator.consolidate(s, v)
        action(s0.copy(retrying = true), v, (s1, r, v1) => Q(s1.copy(retrying = false), r, v1))
      }

    finalActionResult
  }

  def tryOrFail0(s: State, v: Verifier)
                (action: (State, Verifier, (State, Verifier) => VerificationResult) => VerificationResult)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult =

      tryOrFailWithResult[scala.Null](s, v)((s1, v1, QS) => action(s1, v1, (s2, v2) => QS(s2, null, v2)))((s2, `null`, v2) => Q(s2, v2))

  def tryOrFail1[R1](s: State, v: Verifier)
                    (action: (State, Verifier, (State, R1, Verifier) => VerificationResult) => VerificationResult)
                    (Q: (State, R1, Verifier) => VerificationResult)
                    : VerificationResult =

      tryOrFailWithResult[R1](s, v)(action)(Q)

  def tryOrFail2[R1, R2](s: State, v: Verifier)
                        (action: (State, Verifier, (State, R1, R2, Verifier) => VerificationResult) => VerificationResult)
                        (Q: (State, R1, R2, Verifier) => VerificationResult)
                        : VerificationResult =

      tryOrFailWithResult[(R1, R2)](s, v)((s1, v1, QS) => action(s1, v1, (s2, r21, r22, v2) => QS(s2, (r21, r22), v2)))((s2, r, v2) => Q(s2, r._1, r._2, v2))
}
