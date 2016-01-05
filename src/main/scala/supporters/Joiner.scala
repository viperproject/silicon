/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silicon.interfaces.{Success, VerificationResult}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state.{State, PathConditions, Heap, Store, Context}
import viper.silicon.state.DefaultContext
import viper.silicon.state.terms.{App, True, Implies, And, Term, Sort}

case class JoinDataEntry[C <: Context[C], D]
                        (data: D,
                         branchConditions: Seq[Term],
                         πDelta: Set[Term],
                         c: C)

trait Joiner[C <: Context[C]] {
  def join[D, JD](c: C, block: ((D, C) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[C, D]]) => JD)
                 (Q: (JD, C) => VerificationResult)
                 : VerificationResult
}

trait DefaultJoiner[ST <: Store[ST],
                    H <: Heap[H],
                    PC <: PathConditions[PC],
                    S <: State[ST, H, S]]
    extends Joiner[DefaultContext[H]]
{ this: DefaultBrancher[ST, H, PC, S] =>

  private[this] type C = DefaultContext[H]

  val decider: Decider[ST, H, PC, S, C]

  def join[D, JD](c: C, block: ((D, C) => VerificationResult) => VerificationResult)
                 (merge: (Seq[JoinDataEntry[C, D]]) => JD)
                 (Q: (JD, C) => VerificationResult)
                 : VerificationResult = {

    val πInit: Set[Term] = decider.π
    var entries: Seq[JoinDataEntry[C, D]] = Vector.empty

    /* Note: Executing the block in its own scope may result in incompletenesses:
     *   1. Let A be an assumption, e.g., a combine-term, that is added during
     *      the execution of block, but before the block's execution branches
     *   2. When the leaves of the block's execution are combined, A will be placed
     *      under the guards corresponding to the individual leaves; but A should
     *      be unconditional since it was added to the path conditions before
     *      the branching took place.
     */

    /*decider.locally*/ {
      block((data, c1) => {
        val newBranchConditions = c1.branchConditions.filterNot(c.branchConditions.contains)
        val πDelta = decider.π -- πInit -- newBranchConditions
        val c2 = c1.copy(branchConditions = c.branchConditions)

        entries :+= JoinDataEntry(data, newBranchConditions, πDelta, c2)

        Success()
      })
    } && {
      if (entries.isEmpty) {
        /* Note: No block data was collected, which we interpret as all branches through the block
         * being infeasible. Instead of calling Q, we terminate (the current branch of) the
         * verification.
         */
        Success()
      } else {
        val cJoined =
          entries.foldLeft(entries.head.c)((cAcc, localData) => {
            val (πTopLevel, πNested) = viper.silicon.state.utils.partitionAuxiliaryTerms(localData.πDelta)

            decider.prover.logComment("Top-level path conditions")
            decider.assume(πTopLevel)
            decider.prover.logComment("Nested path conditions")
            decider.assume(Implies(And(localData.branchConditions), And(πNested)))

            cAcc.merge(localData.c)
          })

        val joinedData = merge(entries)

        Q(joinedData, cJoined)
      }
    }
  }
}
