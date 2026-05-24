// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silver.ast
import viper.silicon.Config.ExhaleMode
import viper.silicon.interfaces._
import viper.silicon.logger.records.data.CommentRecord
import viper.silicon.state.State
import viper.silicon.supporters.AnnotationSupporter
import viper.silicon.verifier.Verifier

trait ExecutionFlowRules extends SymbolicExecutionRules {
  def locallyWithResult[R](s: State)
                          (block: (State, R => VerificationResult) => VerificationResult)
                          (Q: R => VerificationResult)
                          : VerificationResult

  def locally(s: State)
             (block: State => VerificationResult)
             : VerificationResult

  def tryOrFail0(s: State)
                (action: (State, State => VerificationResult) => VerificationResult)
                (Q: State => VerificationResult)
                : VerificationResult

  def tryOrFail1[R1](s: State)
                    (action: (State, (State, R1) => VerificationResult) => VerificationResult)
                    (Q: (State, R1) => VerificationResult)
                    : VerificationResult

  def tryOrFail2[R1, R2](s: State)
                        (action: (State, (State, R1, R2) => VerificationResult) => VerificationResult)
                        (Q: (State, R1, R2) => VerificationResult)
                        : VerificationResult
}

object executionFlowController extends ExecutionFlowRules {
  def locallyWithResult[R](s: State)
                          (block: (State, R => VerificationResult) => VerificationResult)
                          (Q: R => VerificationResult)
                          : VerificationResult = {

    var optBlockData: Option[R] = None

    s.v.decider.pushScope()

    val blockResult: VerificationResult =
      block(s, blockData => {
        Predef.assert(optBlockData.isEmpty,
                        "Unexpectedly found more than one block data result. Note that the local "
                      + "block is not expected to branch (non-locally)")

        optBlockData = Some(blockData)

        Success()})

    s.v.decider.popScope()

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

  def locally(s: State)
             (block: State => VerificationResult)
             : VerificationResult =

    locallyWithResult[VerificationResult](s)((s1, QL) => QL(block(s1)))(Predef.identity)


  private def tryOrFailWithResult[R](s: State)
                                    (action: (State, (State, R) => VerificationResult) => VerificationResult)
                                    (Q: (State, R) => VerificationResult)
                                    : VerificationResult = {

    var localActionSuccess = false

    /* TODO: Consider how to handle situations where the action branches and the first branch
     *       succeeds, i.e. localActionSuccess has been set to true, but the second fails.
     *       Currently, the verification will fail without attempting to remedy the situation,
     *       e.g. by performing a state consolidation.
     */
    val firstActionResult = {
      action(
        s.copy(retryLevel = s.retryLevel + 1),
        (s1, r) => {
          localActionSuccess = true
          Q(s1.copy(retryLevel = s.retryLevel), r)})
    }

    val finalActionResult =
      if (   localActionSuccess /* Action succeeded locally */
          || !firstActionResult.isFatal) /* Action yielded non-fatal result (e.g. because the
                                          * current branch turned out to be infeasible) */
        firstActionResult
      else {
        val v = s.v
        val s0 = s.consolidate()

        val comLog = new CommentRecord("Retry", s0, v.decider.pcs)
        val sepIdentifier = v.symbExLog.openScope(comLog)
        val temporaryMCE = s0.currentMember.flatMap(AnnotationSupporter.getExhaleMode(_, v.reporter)) match {
          case Some(ExhaleMode.Greedy) =>
            false
          case Some(ExhaleMode.MoreComplete) | Some(ExhaleMode.MoreCompleteOnDemand) =>
            true
          case _ =>
            Verifier.config.exhaleMode != ExhaleMode.Greedy
        }

        action(s0.copy(retrying = true, retryLevel = s.retryLevel)
                  .updateSettings(_.copy(moreCompleteExhale = temporaryMCE)), (s1, r) => {
          v.symbExLog.closeScope(sepIdentifier)
          Q(s1.copy(retrying = false)
              .updateSettings(_.copy(moreCompleteExhale = s0.moreCompleteExhale)), r)
        })
      }

    finalActionResult
  }

  def tryOrFail0(s: State)
                (action: (State, State => VerificationResult) => VerificationResult)
                (Q: State => VerificationResult)
                : VerificationResult =

      tryOrFailWithResult[scala.Null](s)((s1, QS) => action(s1, s2 => QS(s2, null)))((s2, _) => Q(s2))

  def tryOrFail1[R1](s: State)
                    (action: (State, (State, R1) => VerificationResult) => VerificationResult)
                    (Q: (State, R1) => VerificationResult)
                    : VerificationResult =

      tryOrFailWithResult[R1](s)(action)(Q)

  def tryOrFail2[R1, R2](s: State)
                        (action: (State, (State, R1, R2) => VerificationResult) => VerificationResult)
                        (Q: (State, R1, R2) => VerificationResult)
                        : VerificationResult =

      tryOrFailWithResult[(R1, R2)](s)((s1, QS) => action(s1, (s2, r21, r22) => QS(s2, (r21, r22))))((s2, r) => Q(s2, r._1, r._2))
}
