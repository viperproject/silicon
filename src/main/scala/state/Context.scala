/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state

import viper.silver.ast
import viper.silicon.supporters.qps.{SummarisingFvfDefinition, SummarisingPsfDefinition}
import viper.silicon.{Map, Set, Stack}
import viper.silicon.interfaces.state.{Mergeable, Context, Heap}
import viper.silicon.state.terms.{Var, Term}
import viper.silicon.supporters.functions.{NoopFunctionRecorder, FunctionRecorder}

case class DefaultContext[H <: Heap[H]]
                         (program: ast.Program,
                          qpFields: Set[ast.Field],
                          qpPredicates: Set[ast.Predicate],
                          recordVisited: Boolean = false,
                          visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */
                          constrainableARPs: Set[Term] = Set(),
                          quantifiedVariables: Stack[Var] = Nil,
                          retrying: Boolean = false,
                          functionRecorder: FunctionRecorder = NoopFunctionRecorder,
                          recordPossibleTriggers: Boolean = false,
                          possibleTriggers: Map[ast.Exp, Term] = Map(),
                          oldHeaps: Map[String, H] = Map.empty[String, H], /* TODO: Integrate regular old */
                          partiallyConsumedHeap: Option[H] = None,
                          permissionScalingFactor: Term = terms.FullPerm(),

                          reserveHeaps: Stack[H] = Nil,
                          exhaleExt: Boolean = false,
                          lhsHeap: Option[H] = None, /* Used to interpret e in lhs(e) */

                          applyHeuristics: Boolean = false,
                          heuristicsDepth: Int = 0,
                          triggerAction: AnyRef = null,

                          recordEffects: Boolean = false,
                          consumedChunks: Stack[Seq[(Stack[Term], BasicChunk)]] = Nil,
                          letBoundVars: Seq[(ast.AbstractLocalVar, Term)] = Nil,

                          /* TODO: Are these entries still necessary? */
                          fvfCache: Map[(ast.Field, Seq[QuantifiedFieldChunk]), SummarisingFvfDefinition] = Map.empty,
                          fvfPredicateCache: Map[(ast.Predicate, Seq[QuantifiedFieldChunk]), SummarisingFvfDefinition] = Map.empty,
                          fvfAsSnap: Boolean = false,

                          /* TODO: Are these entries still necessary? */
                          psfCache: Map[(ast.Predicate, Seq[QuantifiedPredicateChunk]), SummarisingPsfDefinition] = Map.empty,
                          psfPredicateCache: Map[(ast.Predicate, Seq[QuantifiedPredicateChunk]), SummarisingPsfDefinition] = Map.empty,
                          psfAsSnap: Boolean = false,
                          /* TODO: Isn't this data stable, i.e. fully known after a preprocessing step? If so, move it to the appropriate supporter. */
                          predicateSnapMap:Map[ast.Predicate, terms.Sort] = Map.empty,
                          predicateFormalVarMap:Map[ast.Predicate, Seq[terms.Var]] = Map.empty)

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

  def scalePermissionFactor(p: Term) =
    copy(permissionScalingFactor = terms.PermTimes(p, permissionScalingFactor))

  /* TODO: Instead of aborting right after detecting a mismatch, all mismatches
   *       should be detected first (and accumulated), and only afterwards an
   *       exception should be thrown. This would improve debugging because the
   *       list of accumulated mismatches can be used to generate better debug
   *       output.
   */

  def merge(other: DefaultContext[H]): DefaultContext[H] = this match {
    case DefaultContext(program1, qpFields1, qpPredicates1, recordVisited1, visited1, constrainableARPs1,
                        quantifiedVariables1, retrying1, functionRecorder1, recordPossibleTriggers1,
                        possibleTriggers1, oldHeaps1, partiallyConsumedHeap1, permissionScalingFactor1,
                        reserveHeaps1, exhaleExt1, lhsHeap1,
                        applyHeuristics1, heuristicsDepth1, triggerAction1,
                        recordEffects1, consumedChunks1, letBoundVars1,
                        fvfCache1, fvfPredicateCache1, fvfAsSnap1,
                        psfCache1, psfPredicateCache1, psfAsSnap1, predicateSnapMap1, predicateFormalVarMap1) =>

      other match {
        case DefaultContext(`program1`, `qpFields1`, `qpPredicates1`, recordVisited2, `visited1`,
                            `constrainableARPs1`, `quantifiedVariables1`, retrying2, functionRecorder2,
                            `recordPossibleTriggers1`, possibleTriggers2, `oldHeaps1`, `partiallyConsumedHeap1`, `permissionScalingFactor1`,
                            `reserveHeaps1`, `exhaleExt1`, `lhsHeap1`,
                            `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
                            `recordEffects1`, `consumedChunks1`, `letBoundVars1`,
                            fvfCache2, fvfPredicateCache2, fvfAsSnap2,
                            psfCache2, psfPredicateCache2, psfAsSnap2, predicateSnapMap2, predicateFormalVarMap2) =>

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

          val fvfPredicateCache3 =
            viper.silicon.utils.conflictFreeUnion(fvfPredicateCache1, fvfPredicateCache2) match {
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
                assert(fvfPredicateCache1.size == fvfPredicateCache2.size)
                fvfPredicateCache1
            }

          val psfCache3 =
            viper.silicon.utils.conflictFreeUnion(psfCache1, psfCache2) match {
              case Right(m3) => m3
              case _ =>
                //TODO: Comparing size is not sufficient - we should compare cache entries for
                assert(psfCache1.size == psfCache2.size)
                psfCache1
            }

          val psfPredicateCache3 =
            viper.silicon.utils.conflictFreeUnion(psfPredicateCache1, psfPredicateCache2) match {
              case Right(m3) => m3
              case _ =>
                //TODO: Comparing size is not sufficient - we should compare cache entries for
                assert(psfPredicateCache1.size == psfPredicateCache2.size)
                psfPredicateCache1
            }

          val predicateSnapMap3 : Map[ast.Predicate, terms.Sort] = if (predicateSnapMap1.size > predicateSnapMap2.size) {
            predicateSnapMap1
          } else {
            predicateSnapMap2
          }

          val predicateFormalVarMap3 : Map[ast.Predicate, Seq[terms.Var]] = if (predicateFormalVarMap1.size > predicateFormalVarMap2.size) {
            predicateFormalVarMap1
          } else {
            predicateFormalVarMap2
          }

          copy(recordVisited = recordVisited1 || recordVisited2,
               retrying = retrying1 || retrying2,
               functionRecorder = functionRecorder3,
               possibleTriggers = possibleTriggers3,
               fvfCache = fvfCache3,
               fvfPredicateCache = fvfPredicateCache3,
               fvfAsSnap = fvfAsSnap1 || fvfAsSnap2,
               psfPredicateCache = psfPredicateCache3,
               psfAsSnap = psfAsSnap1 || psfAsSnap2,
               predicateSnapMap = predicateSnapMap3,
               predicateFormalVarMap = predicateFormalVarMap3)



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
