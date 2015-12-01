/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import silver.ast
import interfaces.state.{Context, Mergeable, Heap}
import terms.{Var, Term}
import supporters.SnapshotRecorder

case class DefaultContext[H <: Heap[H]]
                         (program: ast.Program,
                          recordVisited: Boolean = false,
                          visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */
                          branchConditions: Stack[Term] = Stack(),
                          constrainableARPs: Set[Term] = Set(),
                          quantifiedVariables: Stack[Var] = Nil,
                          retrying: Boolean = false,
                          snapshotRecorder: Option[SnapshotRecorder] = None,
                          recordPossibleTriggers: Boolean = false,
                          possibleTriggers: Map[ast.Exp, Term] = Map(),
                          oldHeaps: Map[String, H] = Map.empty[String, H], /* TODO: Integrate regular old */
                          partiallyConsumedHeap: Option[H] = None)
    extends Context[DefaultContext[H]] {

  def incCycleCounter(m: ast.Predicate) =
    if (recordVisited) copy(visited = m :: visited)
    else this

  def decCycleCounter(m: ast.Member) =
    if (recordVisited) {
      require(visited.contains(m))

      val (ms, others) = visited.partition(_ == m)
      copy(visited = ms.tail ::: others)
    }
  else
    this

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Seq[Term], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

  /* TODO: Instead of aborting right after detecting a mismatch, all mismatches
   *       should be detected first (and accumulated), and only afterwards an
   *       exception should be thrown. This would improve debugging because the
   *       list of accumulated mismatches can be used to generate better debug
   *       output.
   */

  def merge(other: DefaultContext[H]): DefaultContext[H] = this match {
    case DefaultContext(program1, recordVisited1, visited1, branchConditions1, constrainableARPs1, quantifiedVariables1,
                        retrying1, snapshotRecorder1, recordPossibleTriggers1, possibleTriggers1, oldHeaps1,
                        partiallyConsumedHeap1) =>

      other match {
        case DefaultContext(`program1`, recordVisited2, `visited1`, `branchConditions1`, `constrainableARPs1`,
                            `quantifiedVariables1`, retrying2, snapshotRecorder2, `recordPossibleTriggers1`,
                            possibleTriggers2, `oldHeaps1`, `partiallyConsumedHeap1`) =>

//          val possibleTriggers3 = DefaultContext.conflictFreeUnionOrAbort(possibleTriggers1, possibleTriggers2)
          val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
          val snapshotRecorder3 = DefaultContext.merge(snapshotRecorder1, snapshotRecorder2)

          copy(recordVisited = recordVisited1 || recordVisited2,
               retrying = retrying1 || retrying2,
               snapshotRecorder = snapshotRecorder3,
               possibleTriggers = possibleTriggers3)

        case _ =>
          sys.error("Unexpected mismatch between contexts")
      }
  }

  override val toString = s"${this.getClass.getSimpleName}(...)"
}

object DefaultContext {
  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K,V] =
    silicon.utils.conflictFreeUnion(m1, m2) match {
      case Right(m3) => m3
      case _ => sys.error("Unexpected mismatch between contexts")
    }

  def merge[M <: Mergeable[M]](candidate1: Option[M], candidate2: Option[M]): Option[M] =
    (candidate1, candidate2) match {
      case (Some(m1), Some(m2)) => Some(m1.merge(m2))
      case (None, None) => None
      case _ => sys.error("Unexpected mismatch between contexts")
    }
}
