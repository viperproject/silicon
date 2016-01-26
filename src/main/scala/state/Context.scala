/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.ast
import viper.silicon.supporters.qps.{SummarisingFvfDefinition}
import viper.silicon.{Map, Set, Stack}
import viper.silicon.interfaces.state.{Mergeable, Context, Heap}
import viper.silicon.state.terms.{Var, Term}
import viper.silicon.supporters.functions.{NoopFunctionRecorder, FunctionRecorder}

case class DefaultContext[H <: Heap[H]]
                         (program: ast.Program,
                          qpFields: Set[ast.Field],
                          recordVisited: Boolean = false,
                          visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */
//                          branchConditions: Stack[Term] = Stack(),
                          constrainableARPs: Set[Term] = Set(),
                          quantifiedVariables: Stack[Var] = Nil,
                          retrying: Boolean = false,
                          functionRecorder: FunctionRecorder = NoopFunctionRecorder,
                          recordPossibleTriggers: Boolean = false,
                          possibleTriggers: Map[ast.Exp, Term] = Map(),
                          oldHeaps: Map[String, H] = Map.empty[String, H], /* TODO: Integrate regular old */
                          partiallyConsumedHeap: Option[H] = None,

                          reserveHeaps: Stack[H] = Nil,
                          exhaleExt: Boolean = false,
                          lhsHeap: Option[H] = None, /* Used to interpret e in ApplyOld(e) */
                          evalHeap: Option[H] = None,

                          applyHeuristics: Boolean = false,
                          heuristicsDepth: Int = 0,
                          triggerAction: AnyRef = null,

                          recordEffects: Boolean = false,
                          producedChunks: Seq[(Stack[Term], BasicChunk)] = Nil,
                          consumedChunks: Stack[Seq[(Stack[Term], BasicChunk)]] = Nil,
                          letBoundVars: Seq[(ast.AbstractLocalVar, Term)] = Nil,

                          fvfCache: Map[(ast.Field, Seq[QuantifiedChunk]), SummarisingFvfDefinition] = Map.empty,
                          fvfAsSnap: Boolean = false)
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
    case DefaultContext(program1, qpFields1, recordVisited1, visited1, /*branchConditions1,*/ constrainableARPs1,
                        quantifiedVariables1, retrying1, functionRecorder1, recordPossibleTriggers1,
                        possibleTriggers1, oldHeaps1, partiallyConsumedHeap1,
                        reserveHeaps1, exhaleExt1, lhsHeap1, evalHeap1,
                        applyHeuristics1, heuristicsDepth1, triggerAction1,
                        recordEffects1, producedChunks1, consumedChunks1, letBoundVars1,
                        fvfCache1, fvfAsSnap1) =>

      other match {
        case DefaultContext(`program1`, `qpFields1`, recordVisited2, `visited1`, /*`branchConditions1`,*/
                            `constrainableARPs1`, `quantifiedVariables1`, retrying2, functionRecorder2,
                            `recordPossibleTriggers1`, possibleTriggers2, `oldHeaps1`, `partiallyConsumedHeap1`,
                            `reserveHeaps1`, `exhaleExt1`, `lhsHeap1`, `evalHeap1`,
                            `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
                            `recordEffects1`, `producedChunks1`, `consumedChunks1`, `letBoundVars1`,
                            fvfCache2, fvfAsSnap2) =>

//          val possibleTriggers3 = DefaultContext.conflictFreeUnionOrAbort(possibleTriggers1, possibleTriggers2)
          val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
          val functionRecorder3 = functionRecorder1.merge(functionRecorder2)

          val fvfCache3 =
            viper.silicon.utils.conflictFreeUnion(fvfCache1, fvfCache2) match {
              case Right(m3) => m3
              case _ =>
                /* TODO: Comparing size is not sufficient - we should compare cache entries for
                 *       equality modulo renaming of FVFs.
                 *       Even better: when branching (locally/in general?), there the fvfCache from the
                 *       first branch should be made available to the second branch in order to avoid
                 *       axiomatising a fresh but equivalent FVF.
                 *       This should be sound because the branch condition (of a local branch?) cannot
                 *       influence the available chunks.
                 */
                assert(fvfCache1.size == fvfCache2.size)
                fvfCache1
            }

          copy(recordVisited = recordVisited1 || recordVisited2,
               retrying = retrying1 || retrying2,
               functionRecorder = functionRecorder3,
               possibleTriggers = possibleTriggers3,
               fvfCache = fvfCache3,
               fvfAsSnap = fvfAsSnap1 || fvfAsSnap2)

        case _ =>
//          println("\n[Context.merge]")
//          println("--this--")
//          this.productIterator.toSeq.tail foreach println
//          println("--other--")
//          other.productIterator.toSeq.tail foreach println

          sys.error("Unexpected mismatch between contexts")
      }
  }

  override val toString = s"${this.getClass.getSimpleName}(...)"
}

object DefaultContext {
  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K,V] =
    viper.silicon.utils.conflictFreeUnion(m1, m2) match {
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
