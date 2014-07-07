/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon
package reporting

import interfaces.state.{ Store, Heap, State}
import interfaces.reporting.{ Context, Branch, BranchingStep}
import state.terms.Term

/* TODO: Use MultiSet[Member] instead of List[Member] */
case class DefaultContext[ST <: Store[ST],
                          H <: Heap[H],
                          S <: State[ST, H, S]]
                         (program: ast.Program,
                          currentBranch: Branch[ST, H, S],
                          visited: List[ast.Member] = Nil,
                          constrainableARPs: Set[Term] = Set())
    extends Context[DefaultContext[ST, H, S], ST, H, S] {

  def replaceCurrentBranch(currentBranch: Branch[ST, H, S]): DefaultContext[ST, H, S] =
    copy(currentBranch = currentBranch)

  def incCycleCounter(m: ast.Member) = copy(visited = m :: visited)

  def decCycleCounter(m: ast.Member) = {
    require(visited.contains(m))

    val (ms, others) = visited.partition(_ == m)
    copy(visited = ms.tail ::: others)
  }

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Seq[Term], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

	lazy val branchings: List[BranchingStep[ST, H, S]] = currentBranch.branchings
}
