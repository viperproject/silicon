// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces._
import viper.silicon.state.State
import viper.silicon.verifier.Verifier

trait ExecutionFlowRules extends SymbolicExecutionRules {
  def locallyWithResult[R](s: State, v: Verifier)
                          (block: (State, Verifier, R => VerificationResultWrapper) => VerificationResultWrapper)
                          (Q: R => VerificationResultWrapper)
                          : VerificationResultWrapper

  def locally(s: State, v: Verifier)
             (block: (State, Verifier) => VerificationResultWrapper)
             : VerificationResultWrapper

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
                (action: (State, Verifier, (State, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                (Q: (State, Verifier) => VerificationResultWrapper)
                : VerificationResultWrapper

  def tryOrFail1[R1](s: State, v: Verifier)
                    (action: (State, Verifier, (State, R1, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                    (Q: (State, R1, Verifier) => VerificationResultWrapper)
                    : VerificationResultWrapper

  def tryOrFail2[R1, R2](s: State, v: Verifier)
                        (action: (State, Verifier, (State, R1, R2, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                        (Q: (State, R1, R2, Verifier) => VerificationResultWrapper)
                        : VerificationResultWrapper
}

object executionFlowController extends ExecutionFlowRules {
  def locallyWithResult[R](s: State, v: Verifier)
                          (block: (State, Verifier, R => VerificationResultWrapper) => VerificationResultWrapper)
                          (Q: R => VerificationResultWrapper)
                          : VerificationResultWrapper = {

    var optBlockData: Option[R] = None

    v.decider.pushScope()

    val blockResult: VerificationResultWrapper =
      block(s, v, blockData => {
        Predef.assert(optBlockData.isEmpty,
                        "Unexpectedly found more than one block data result. Note that the local "
                      + "block is not expected to branch (non-locally)")

        optBlockData = Some(blockData)

        VerificationResultWrapper(Success())})

    v.decider.popScope()
    val res = if(blockResult.containsFatal){ //TODO:J add comments
      blockResult
    }else{
      optBlockData match {
        case Some(localData) => blockResult && Q(localData)
        case None => blockResult
      }
    }
    res
  }

  def locally(s: State, v: Verifier)
             (block: (State, Verifier) => VerificationResultWrapper)
             : VerificationResultWrapper =

    locallyWithResult[VerificationResultWrapper](s, v)((s1, v1, QL) => QL(block(s1, v1)))(Predef.identity)


  private def tryOrFailWithResult[R](s: State, v: Verifier)
                                    (action: (State, Verifier, (State, R, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                                    (Q: (State, R, Verifier) => VerificationResultWrapper)
                                    : VerificationResultWrapper = {

    var localActionSuccess = false

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
          || !firstActionResult.containsFatal) /* Action yielded non-fatal result (e.g. because the
                                          * current branch turned out to be infeasible) */
        firstActionResult
      else {
        val s0 = stateConsolidator.consolidate(s, v)
        action(s0.copy(retrying = true), v, (s1, r, v1) => Q(s1.copy(retrying = false), r, v1))
      }

    finalActionResult
  }

  def tryOrFail0(s: State, v: Verifier)
                (action: (State, Verifier, (State, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                (Q: (State, Verifier) => VerificationResultWrapper)
                : VerificationResultWrapper =

      tryOrFailWithResult[scala.Null](s, v)((s1, v1, QS) => action(s1, v1, (s2, v2) => QS(s2, null, v2)))((s2, _, v2) => Q(s2, v2))

  def tryOrFail1[R1](s: State, v: Verifier)
                    (action: (State, Verifier, (State, R1, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                    (Q: (State, R1, Verifier) => VerificationResultWrapper)
                    : VerificationResultWrapper =

      tryOrFailWithResult[R1](s, v)(action)(Q)

  def tryOrFail2[R1, R2](s: State, v: Verifier)
                        (action: (State, Verifier, (State, R1, R2, Verifier) => VerificationResultWrapper) => VerificationResultWrapper)
                        (Q: (State, R1, R2, Verifier) => VerificationResultWrapper)
                        : VerificationResultWrapper =

      tryOrFailWithResult[(R1, R2)](s, v)((s1, v1, QS) => action(s1, v1, (s2, r21, r22, v2) => QS(s2, (r21, r22), v2)))((s2, r, v2) => Q(s2, r._1, r._2, v2))
}
