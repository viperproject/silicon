// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import java.util.concurrent._
import viper.silicon.common.concurrency._
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.state.State
import viper.silicon.state.terms.{FunctionDecl, MacroDecl, Not, Term}
import viper.silicon.verifier.Verifier
import viper.silver.ast

trait BranchingRules extends SymbolicExecutionRules {
  def branch(s: State,
             condition: Term,
             conditionExp: Option[ast.Exp],
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fTrue: (State, Verifier) => VerificationResult,
             fFalse: (State, Verifier) => VerificationResult)
            : VerificationResult
}

object brancher extends BranchingRules {
  def branch(s: State,
             condition: Term,
             conditionExp: Option[ast.Exp],
             v: Verifier,
             fromShortCircuitingAnd: Boolean = false)
            (fThen: (State, Verifier) => VerificationResult,
             fElse: (State, Verifier) => VerificationResult)
            : VerificationResult = {

    val negatedCondition = Not(condition)
    val negatedConditionExp = conditionExp.fold[Option[ast.Exp]](None)(c => Some(ast.Not(c)(pos = conditionExp.get.pos, info = conditionExp.get.info, ast.NoTrafos)))


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

    val parallelizeElseBranch = s.parallelizeBranches && !s.underJoin && executeThenBranch && executeElseBranch

//    val additionalPaths =
//      if (executeThenBranch && exploreFalseBranch) 1
//      else 0

//    bookkeeper.branches += additionalPaths

    val cnt = v.counter(this).next()

    val thenBranchComment = s"[then-branch: $cnt | $condition | ${if (executeThenBranch) "live" else "dead"}]"
    val elseBranchComment = s"[else-branch: $cnt | $negatedCondition | ${if (executeElseBranch) "live" else "dead"}]"

    v.decider.prover.comment(thenBranchComment)
    v.decider.prover.comment(elseBranchComment)

    var elseBranchVerifier: String = null

    val uidBranchPoint = v.symbExLog.insertBranchPoint(2, Some(condition), conditionExp)
    var functionsOfCurrentDecider: Set[FunctionDecl] = null
    var macrosOfCurrentDecider: Vector[MacroDecl] = null
    var pcsForElseBranch: PathConditionStack = null

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
        if (parallelizeElseBranch){
          functionsOfCurrentDecider = v.decider.freshFunctions
          macrosOfCurrentDecider = v.decider.freshMacros
          pcsForElseBranch = v.decider.pcs.duplicate()
        }

        (v0: Verifier) => {
          v0.symbExLog.switchToNextBranch(uidBranchPoint)
          v0.symbExLog.markReachable(uidBranchPoint)
          if (v.uniqueId != v0.uniqueId){
            /* [BRANCH-PARALLELISATION] */
            // executing the else branch on a different verifier, need to adapt the state

            val newFunctions = functionsOfCurrentDecider -- v0.decider.freshFunctions
            val newMacros = macrosOfCurrentDecider.diff(v0.decider.freshMacros)

            v0.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v0.uniqueId}]")
            v0.decider.prover.comment(s"Bulk-declaring functions")
            v0.decider.declareAndRecordAsFreshFunctions(newFunctions)
            v0.decider.prover.comment(s"Bulk-declaring macros")
            v0.decider.declareAndRecordAsFreshMacros(newMacros)

            v0.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
            v0.decider.setPcs(pcsForElseBranch)
          }
          elseBranchVerifier = v0.uniqueId

          executionFlowController.locally(s, v0)((s1, v1) => {
            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            v1.decider.setCurrentBranchCondition(negatedCondition, negatedConditionExp)

            if (v.uniqueId != v0.uniqueId)
              v1.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)

            fElse(v1.stateConsolidator.consolidateIfRetrying(s1, v1), v1)
          })
        }
      } else {
        _ => Unreachable()
      }

    val elseBranchFuture: Future[Seq[VerificationResult]] =
      if (executeElseBranch) {
        if (parallelizeElseBranch) {
          /* [BRANCH-PARALLELISATION] */
          v.verificationPoolManager.queueVerificationTask(v0 => {
            val res = elseBranchVerificationTask(v0)

            Seq(res)
          })
        } else {
          new SynchronousFuture(Seq(elseBranchVerificationTask(v)))
        }
      } else {
        CompletableFuture.completedFuture(Seq(Unreachable()))
      }

    val res = (if (executeThenBranch) {
      v.symbExLog.markReachable(uidBranchPoint)
      executionFlowController.locally(s, v)((s1, v1) => {
        v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
        v1.decider.setCurrentBranchCondition(condition, conditionExp)

        fThen(v1.stateConsolidator.consolidateIfRetrying(s1, v1), v1)
      })
    } else {
      Unreachable()
    }).combine({

      /* [BRANCH-PARALLELISATION] */
      var rs: Seq[VerificationResult] = null
      try {
        if (parallelizeElseBranch) {
          val pcsAfterThenBranch = v.decider.pcs.duplicate()

          val pcsBefore = v.decider.pcs

          rs = elseBranchFuture.get()

          if (v.decider.pcs != pcsBefore && v.uniqueId != elseBranchVerifier){
            // we have done other work during the join, need to reset
            v.decider.prover.comment(s"Resetting path conditions after interruption")
            v.decider.setPcs(pcsAfterThenBranch)
            v.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
          }
        }else{
          rs = elseBranchFuture.get()
        }
      } catch {
        case ex: ExecutionException =>
          ex.getCause.printStackTrace()
          throw ex
      }

      assert(rs.length == 1, s"Expected a single verification result but found ${rs.length}")
      rs.head

    }, alwaysWaitForOther = parallelizeElseBranch)
    v.symbExLog.endBranchPoint(uidBranchPoint)
    res
  }
}
