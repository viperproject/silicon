/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.state.State
import viper.silicon.state.terms.{Not, Term}
import viper.silicon.verifier.Verifier

trait BranchingRules extends SymbolicExecutionRules {
  def branch(s: State,
             condition: Term,
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fTrue: (State, Verifier) => VerificationResult,
             fFalse: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object brancher extends BranchingRules with Immutable {
  def branch(s: State,
             condition: Term,
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fThen: (State, Verifier) => VerificationResult,
             fElse: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val negatedCondition = Not(condition)
    val parallelizeElseBranch = s.parallelizeBranches && !s.underJoin

    /* Skip path feasibility check if one of the following holds:
     *   (1) the branching is due to the short-circuiting evaluation of a conjunction
     *   (2) the branch condition contains a quantified variable
     */
    val skipPathFeasibilityCheck = (
         fromShortCircuitingAnd
      || (   s.quantifiedVariables.nonEmpty
          && s.quantifiedVariables.exists(condition.freeVariables.contains))
    )

    /* True if the then-branch is to be explored */
    val executeThenBranch = (
         skipPathFeasibilityCheck
      || !v.decider.check(negatedCondition, Verifier.config.checkTimeout()))

    /* False if the then-branch is to be explored */
    val executeElseBranch = (
         !executeThenBranch /* Assumes that ast least one branch is feasible */
      || skipPathFeasibilityCheck
      || !v.decider.check(condition, Verifier.config.checkTimeout()))

//    val additionalPaths =
//      if (executeThenBranch && exploreFalseBranch) 1
//      else 0

//    bookkeeper.branches += additionalPaths

    val cnt = v.counter(this).next()

    val thenBranchComment = s"[then-branch: $cnt | $condition | ${if (executeThenBranch) "live" else "dead"}]"
    val elseBranchComment = s"[else-branch: $cnt | $negatedCondition | ${if (executeElseBranch) "live" else "dead"}]"

    v.decider.prover.comment(thenBranchComment)
    v.decider.prover.comment(elseBranchComment)

    val elseBranchVerificationTask: Verifier => VerificationResult =
      if (executeElseBranch) {
/* [BRANCH-PARALLELISATION] */
        /* Compute the following sets
         *   1. only if the else-branch needs to be explored
         *   2. right now, i.e. not when the exploration actually takes place
         * The first requirement avoids computing the sets in cases where they are not
         * needed, the second one ensures that the current path conditions (etc.) of the
         * "offloading" verifier are captured.
         */
//        val functionsOfCurrentDecider = v.decider.freshFunctions
//        val macrosOfCurrentDecider = v.decider.freshMacros
//        val pcsOfCurrentDecider = v.decider.pcs.duplicate()

//        println(s"\n[INIT elseBranchVerificationTask v.uniqueId = ${v.uniqueId}]")
//        println(s"  condition = $condition")
//        println("  v.decider.pcs.assumptions = ")
//        v.decider.pcs.assumptions foreach (a => println(s"    $a"))
//        println("  v.decider.pcs.branchConditions = ")
//        v.decider.pcs.branchConditions foreach (a => println(s"    $a"))

        (v0: Verifier) => {
          executionFlowController.locally(s, v0)((s1, v1) => {
            if (v.uniqueId != v1.uniqueId) {

              /* [BRANCH-PARALLELISATION] */
              throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")

//                val newFunctions = functionsOfCurrentDecider -- v1.decider.freshFunctions
//                val newMacros = macrosOfCurrentDecider.diff(v1.decider.freshMacros)
//
//                v1.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v1.uniqueId}]")
//                v1.decider.prover.comment(s"Bulk-declaring functions")
//                v1.decider.declareAndRecordAsFreshFunctions(newFunctions)
//                v1.decider.prover.comment(s"Bulk-declaring macros")
//                v1.decider.declareAndRecordAsFreshMacros(newMacros)
//
//                v1.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
//                v1.decider.setPcs(pcsOfCurrentDecider)
//                v1.decider.pcs.pushScope() /* Empty scope for which the branch condition can be set */
            }

            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            v1.decider.setCurrentBranchCondition(negatedCondition)

            fElse(stateConsolidator.consolidateIfRetrying(s1, v1), v1)
          })
        }
      } else {
        _ => Unreachable()
      }

    val elseBranchFuture: Future[Seq[VerificationResult]] =
      if (executeElseBranch) {
        if (parallelizeElseBranch) {
          /* [BRANCH-PARALLELISATION] */
          throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")
//          v.verificationPoolManager.queueVerificationTask(v0 => {
//            v0.verificationPoolManager.runningVerificationTasks.put(elseBranchVerificationTask, true)
//            val res = elseBranchVerificationTask(v0)
//
//            v0.verificationPoolManager.runningVerificationTasks.remove(elseBranchVerificationTask)
//
//            Seq(res)
//          })
        } else {
          new SynchronousFuture(Seq(elseBranchVerificationTask(v)))
        }
      } else {
        CompletableFuture.completedFuture(Seq(Unreachable()))
      }

    (if (executeThenBranch) {
      executionFlowController.locally(s, v)((s1, v1) => {
        v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
        v1.decider.setCurrentBranchCondition(condition)

        fThen(stateConsolidator.consolidateIfRetrying(s1, v1), v1)
      })
    } else {
      Unreachable()
    }) && {

      /* [BRANCH-PARALLELISATION] */
      if (parallelizeElseBranch) {
//          && v.verificationPoolManager.slaveVerifierPool.getNumIdle == 0
//          && !v.verificationPoolManager.runningVerificationTasks.containsKey(elseBranchVerificationTask)
//                /* TODO: This attempt to ensure that the elseBranchVerificationTask is not already
//                 *       being executed is most likely not thread-safe since checking if a task
//                 *       is still in the queue and canceling it, if so, is not an atomic operation.
//                 *       I.e. the task may be taken out of the queue in between.
//                 */

        throw new RuntimeException("Branch parallelisation is expected to be deactivated for now")

//        /* Cancelling the task should result in the underlying task being removed from the task
//         * queue/executor
//         */
//        elseBranchFuture.cancel(true)
//
//        /* Run the task on the current thread */
//        elseBranchVerificationTask(v)
      } else {
        var rs: Seq[VerificationResult] = null
        try {
          rs = elseBranchFuture.get()
        } catch {
          case ex: ExecutionException =>
            ex.getCause.printStackTrace()
            throw ex
        }

        assert(rs.length == 1, s"Expected a single verification result but found ${rs.length}")
        rs.head
      }
    }
  }
}
