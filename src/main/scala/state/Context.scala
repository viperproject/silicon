/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state

import interfaces.state.{Context, Mergeable}
import state.terms.{FApp, Term, Var}
import theories.SnapshotRecorder

case class DefaultContext(program: ast.Program,
                          visited: List[ast.Member] = Nil, /* TODO: Use MultiSet[Member] instead of List[Member] */
                          constrainableARPs: Set[Term] = Set(),
                          quantifiedVariables: Stack[Var] = Nil,
                          additionalTriggers: List[Term] = Nil,
                          snapshotRecorder: Option[SnapshotRecorder] = None,
                          fapps: Map[ast.FuncApp, FApp] = Map())
    extends Context[DefaultContext] {

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

  /* TODO: Instead of aborting right after detecting a mismatch, all mismatches
   *       should be detected first (and accumulated), and only afterwards an
   *       exception should be thrown. This would improve debugging because the
   *       list of accumulated mismatches can be used to generate better debug
   *       output.
   */

  def merge(other: DefaultContext): DefaultContext = this match {
    case DefaultContext(program1, visited1, constrainableARPs1, quantifiedVariables1, additionalTriggers1, snapshotRecorder1, fapps1) =>
      other match {
        case DefaultContext(`program1`, `visited1`, `constrainableARPs1`, `quantifiedVariables1`, additionalTriggers2, snapshotRecorder2, fapps2) =>
          val additionalTriggers3 = additionalTriggers1 ++ additionalTriggers2
          val fapps3 = DefaultContext.conflictFreeUnionOrAbort(fapps1, fapps2)
          val snapshotRecorder3 = DefaultContext.merge(snapshotRecorder1, snapshotRecorder2)

          copy(additionalTriggers = additionalTriggers3, snapshotRecorder = snapshotRecorder3, fapps = fapps3)

        case _ =>
          sys.error("Unexpected mismatch between contexts")
      }
  }
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
