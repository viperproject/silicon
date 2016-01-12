/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state.{State, Heap, Store, Context}
import viper.silicon.state.DefaultContext

case class JoinDataEntry[C <: Context[C], D]
                        (data: D,
                         pathConditionStack: PathConditionStack,
                         c: C)

trait Joiner[C <: Context[C]] {
  def join[D, JD](c: C, block: ((D, C) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[C, D]]) => JD)
                 (Q: (JD, C) => VerificationResult)
                 : VerificationResult
}

trait DefaultJoiner[ST <: Store[ST],
                    H <: Heap[H],
                    S <: State[ST, H, S]]
    extends Joiner[DefaultContext[H]]
{ this: DefaultBrancher[ST, H, S] =>

  private[this] type C = DefaultContext[H]

  val decider: Decider[ST, H, S, C]

  def join[D, JD](c: C, block: ((D, C) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[C, D]]) => JD)
                 (Q: (JD, C) => VerificationResult)
                 : VerificationResult = {

    var entries: Seq[JoinDataEntry[C, D]] = Vector.empty

    /* Note: Executing the block in its own scope may result in incompletenesses:
     *   1. Let A be an assumption, e.g., a combine-term, that is added during
     *      the execution of block, but before the block's execution branches
     *   2. When the leaves of the block's execution are combined, A will be placed
     *      under the guards corresponding to the individual leaves; but A should
     *      be unconditional since it was added to the path conditions before
     *      the branching took place.
     */

    decider.locally {
      val preMark = decider.setPathConditionMark()

      block((data, c1) => {
        entries :+= JoinDataEntry(data, decider.pcs.after(preMark), c1)
        Success()
      })
    } && {
      if (entries.isEmpty) {
        /* Note: No block data was collected, which we interpret as all branches through
         * the block being infeasible. In turn, we assume that the overall verification path
         * is infeasible. Instead of calling Q, we therefore terminate this path.
         */
        Success()
      } else {
        /* Note: Modifying the branchConditions before merging contexts is only necessary
         * because DefaultContext.merge (correctly) insists on equal branchConditions,
         * which cannot be circumvented/special-cased when merging contexts here.
         */

        val cInit = entries.head.c

        val cJoined =
          entries.foldLeft(cInit)((cAcc, localData) => {
            val pcs = localData.pathConditionStack.asConditionals
            decider.prover.logComment("Joined path conditions")
            decider.assume(pcs)

            cAcc.merge(localData.c)
          })

        val joinedData = merge(entries)

        Q(joinedData, cJoined)
      }
    }
  }
}
