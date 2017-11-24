/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier

case class JoinDataEntry[D](s: State, data: D, pathConditions: RecordedPathConditions)

trait JoiningRules extends SymbolicExecutionRules {
  def join[D, JD](s: State, v: Verifier)
                 (block: (State, Verifier, (State, D, Verifier) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[D]]) => (State, JD))
                 (Q: (State, JD, Verifier) => VerificationResult)
                 : VerificationResult
}

object joiner extends JoiningRules with Immutable {
  def join[D, JD](s: State, v: Verifier)
                 (block: (State, Verifier, (State, D, Verifier) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[D]]) => (State, JD))
                 (Q: (State, JD, Verifier) => VerificationResult)
                 : VerificationResult = {

    var entries: Seq[JoinDataEntry[D]] = Vector.empty

    executionFlowController.locally(s, v)((s1, v1) => {
      val preMark = v1.decider.setPathConditionMark()
      val s2 = s1.copy(underJoin = true)

      block(s2, v1, (s3, data, v2) => {
        /* In order to prevent mismatches between different final states of the evaluation
         * paths that are to be joined, we reset certain state properties that may have been
         * affected by the evaluation - such as the store (by let-bindings) or the heap (by
         * state consolidations) to their initial values.
         */
        val s4 = s3.copy(g = s1.g,
                         h = s1.h,
                         oldHeaps = s1.oldHeaps,
                         underJoin = s1.underJoin)
        entries :+= JoinDataEntry(s4, data, v2.decider.pcs.after(preMark))
        Success()
      })
    }) && {
      if (entries.isEmpty) {
        /* No block data was collected, which we interpret as all branches through
         * the block being infeasible. In turn, we assume that the overall verification path
         * is infeasible. Instead of calling Q, we therefore terminate this path.
         */
        Success()
      } else {
        val (sJoined, dataJoined) = merge(entries)

        entries foreach (entry => {
          val pcs = entry.pathConditions.conditionalized
          v.decider.prover.comment("Joined path conditions")
          v.decider.assume(pcs)
        })

        Q(sJoined, dataJoined, v)
      }
    }
  }
}
