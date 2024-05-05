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
import viper.silicon.reporting.condenseToViperResult
import viper.silicon.state.State
import viper.silicon.state.terms.{FunctionDecl, MacroDecl, Not, Term}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.reporter.{BranchFailureMessage}
import viper.silver.verifier.Failure

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

    val parallelizeElseBranch = s.parallelizeBranches && executeThenBranch && executeElseBranch

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
    var proverArgsOfCurrentDecider: viper.silicon.Map[String, String] = null
    var wasElseExecutedOnDifferentVerifier = false
    var functionsOfElseBranchDecider: Set[FunctionDecl] = null
    var proverArgsOfElseBranchDecider: viper.silicon.Map[String, String] = null
    var macrosOfElseBranchDecider: Seq[MacroDecl] = null
    var pcsForElseBranch: PathConditionStack = null
    var noOfErrors = 0

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
          proverArgsOfCurrentDecider = v.decider.getProverOptions()
          pcsForElseBranch = v.decider.pcs.duplicate()
          noOfErrors = v.errorsReportedSoFar.get()
        }

        (v0: Verifier) => {
          v0.symbExLog.switchToNextBranch(uidBranchPoint)
          v0.symbExLog.markReachable(uidBranchPoint)
          if (v.uniqueId != v0.uniqueId){
            /* [BRANCH-PARALLELISATION] */
            // executing the else branch on a different verifier, need to adapt the state
            wasElseExecutedOnDifferentVerifier = true

            if (s.underJoin)
              v0.decider.pushSymbolStack()
            val newFunctions = functionsOfCurrentDecider -- v0.decider.freshFunctions
            val newMacros = macrosOfCurrentDecider.diff(v0.decider.freshMacros)

            v0.decider.prover.comment(s"[Shifting execution from ${v.uniqueId} to ${v0.uniqueId}]")
            proverArgsOfElseBranchDecider = v0.decider.getProverOptions()
            v0.decider.resetProverOptions()
            v0.decider.setProverOptions(proverArgsOfCurrentDecider)
            v0.decider.prover.comment(s"Bulk-declaring functions")
            v0.decider.declareAndRecordAsFreshFunctions(newFunctions, false)
            v0.decider.prover.comment(s"Bulk-declaring macros")
            v0.decider.declareAndRecordAsFreshMacros(newMacros, false)

            v0.decider.prover.comment(s"Taking path conditions from source verifier ${v.uniqueId}")
            v0.decider.setPcs(pcsForElseBranch)
            v0.errorsReportedSoFar.set(noOfErrors)
          }
          elseBranchVerifier = v0.uniqueId

          executionFlowController.locally(s, v0)((s1, v1) => {
            v1.decider.prover.comment(s"[else-branch: $cnt | $negatedCondition]")
            v1.decider.setCurrentBranchCondition(negatedCondition, negatedConditionExp)

            if (v.uniqueId != v0.uniqueId)
              v1.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)

            val result = fElse(v1.stateConsolidator(s1).consolidateOptionally(s1, v1), v1)
            if (wasElseExecutedOnDifferentVerifier) {
              v1.decider.resetProverOptions()
              v1.decider.setProverOptions(proverArgsOfElseBranchDecider)
              if (s.underJoin) {
                val newSymbols = v1.decider.popSymbolStack()
                functionsOfElseBranchDecider = newSymbols._1
                macrosOfElseBranchDecider = newSymbols._2
              }
            }
            result
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

    val res = {
      val thenRes = if (executeThenBranch) {
          v.symbExLog.markReachable(uidBranchPoint)
          executionFlowController.locally(s, v)((s1, v1) => {
            v1.decider.prover.comment(s"[then-branch: $cnt | $condition]")
            v1.decider.setCurrentBranchCondition(condition, conditionExp)

            fThen(v1.stateConsolidator(s1).consolidateOptionally(s1, v1), v1)
          })
        } else {
          Unreachable()
        }
      if (thenRes.isFatal && !thenRes.isReported && s.parallelizeBranches && s.isLastRetry) {
        thenRes.isReported = true
        v.reporter.report(BranchFailureMessage("silicon", s.currentMember.get.asInstanceOf[ast.Member with Serializable],
          condenseToViperResult(Seq(thenRes)).asInstanceOf[Failure]))
      }
      thenRes
    }.combine({

      /* [BRANCH-PARALLELISATION] */
      var rs: Seq[VerificationResult] = null
      try {
        if (parallelizeElseBranch) {
          val pcsAfterThenBranch = v.decider.pcs.duplicate()
          val noOfErrorsAfterThenBranch = v.errorsReportedSoFar.get()

          val pcsBefore = v.decider.pcs

          rs = elseBranchFuture.get()

          if (v.decider.pcs != pcsBefore && v.uniqueId != elseBranchVerifier){
            // we have done other work during the join, need to reset
            v.decider.prover.comment(s"Resetting path conditions after interruption")
            v.decider.setPcs(pcsAfterThenBranch)
            v.errorsReportedSoFar.set(noOfErrorsAfterThenBranch)
            v.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
            v.decider.resetProverOptions()
            v.decider.setProverOptions(proverArgsOfCurrentDecider)
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
      if (rs.head.isFatal && !rs.head.isReported && s.parallelizeBranches && s.isLastRetry) {
        rs.head.isReported = true
        v.reporter.report(BranchFailureMessage("silicon", s.currentMember.get.asInstanceOf[ast.Member with Serializable],
          condenseToViperResult(Seq(rs.head)).asInstanceOf[Failure]))
      }
      rs.head

    }, alwaysWaitForOther = parallelizeElseBranch)
    v.symbExLog.endBranchPoint(uidBranchPoint)
    if (wasElseExecutedOnDifferentVerifier && s.underJoin) {

      v.decider.prover.comment(s"[To continue after join, adding else branch functions and macros to current verifier.]")
      v.decider.prover.comment(s"Bulk-declaring functions")
      v.decider.declareAndRecordAsFreshFunctions(functionsOfElseBranchDecider, true)
      v.decider.prover.comment(s"Bulk-declaring macros")
      // Declare macros without duplicates; we keep only the last occurrence of every declaration to avoid errors.
      v.decider.declareAndRecordAsFreshMacros(macrosOfElseBranchDecider.reverse.distinct.reverse, true)
    }
    res
  }
}
