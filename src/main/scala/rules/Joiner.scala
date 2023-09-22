// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import debugger.DebugExp
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.logger.records.structural.JoiningRecord
import viper.silicon.state.State
import viper.silicon.state.terms.{And, Or, Term}
import viper.silicon.utils.ast
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Bool, Exp, LocalVar}

case class JoinDataEntry[D](s: State, data: D, dataExp: Exp, pathConditions: RecordedPathConditions)

trait JoiningRules extends SymbolicExecutionRules {
  def join[D, JD](s: State, v: Verifier)
                 (block: (State, Verifier, (State, D, Exp, Verifier) => VerificationResult) => VerificationResult)
                 (merge: Seq[JoinDataEntry[D]] => (State, JD, Exp))
                 (Q: (State, JD, Exp, Verifier) => VerificationResult)
                 : VerificationResult
}

object joiner extends JoiningRules {
  def join[D, JD](s: State, v: Verifier)
                 (block: (State, Verifier, (State, D, Exp, Verifier) => VerificationResult) => VerificationResult)
                 (merge: Seq[JoinDataEntry[D]] => (State, JD, Exp))
                 (Q: (State, JD, Exp, Verifier) => VerificationResult)
                 : VerificationResult = {

    var entries: Seq[JoinDataEntry[D]] = Vector.empty

    val joiningRecord = new JoiningRecord(s, v.decider.pcs)
    val uidJoin = v.symbExLog.openScope(joiningRecord)

    executionFlowController.locally(s, v)((s1, v1) => {
      val preMark = v1.decider.setPathConditionMark()
      val s2 = s1.copy(underJoin = true)

      block(s2, v1, (s3, data, e, v2) => {
        /* In order to prevent mismatches between different final states of the evaluation
         * paths that are to be joined, we reset certain state properties that may have been
         * affected by the evaluation - such as the store (by let-bindings) or the heap (by
         * state consolidations) to their initial values.
         */
        val s4 = s3.copy(g = s1.g,
                         h = s1.h,
                         oldHeaps = s1.oldHeaps,
                         underJoin = s1.underJoin,
                         retrying = s1.retrying)
        entries :+= JoinDataEntry(s4, data, e, v2.decider.pcs.after(preMark))
        Success()
      })
    }) combine {
      v.symbExLog.closeScope(uidJoin)
      if (entries.isEmpty) {
        /* No block data was collected, which we interpret as all branches through
         * the block being infeasible. In turn, we assume that the overall verification path
         * is infeasible. Instead of calling Q, we therefore terminate this path.
         */
        Success()
      } else {
        val (sJoined, dataJoined, dataJoinedExp) = merge(entries)

        var feasibleBranches: List[Term] = Nil
        var feasibleBranchesExp: List[Exp] = Nil
        var feasibleBranchesExpNew: List[Exp] = Nil

        entries foreach (entry => {
          val pcs = entry.pathConditions.conditionalized
          val pcsExp = entry.pathConditions.conditionalizedExp
          val comment = "Joined path conditions"
          v.decider.prover.comment(comment)
          v.decider.assume(pcs, new DebugExp(comment, InsertionOrderedSet(pcsExp)))
          feasibleBranches = And(entry.pathConditions.branchConditions) :: feasibleBranches
          feasibleBranchesExp = BigAnd(entry.pathConditions.branchConditionExps.map(_.getFirst)) :: feasibleBranchesExp
          feasibleBranchesExpNew = BigAnd(entry.pathConditions.branchConditionExps.map(_.getSecond)) :: feasibleBranchesExpNew
        })
        // Assume we are in a feasible branch
        v.decider.assume(Or(feasibleBranches), new DebugExp(Some("Feasible Branches"), Some(ast.BigOr(feasibleBranchesExp)), Some(ast.BigOr(feasibleBranchesExpNew)), InsertionOrderedSet.empty))
        Q(sJoined, dataJoined, dataJoinedExp, v)
      }
    }
  }
}
