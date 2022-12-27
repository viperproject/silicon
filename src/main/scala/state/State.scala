// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silver.cfg.silver.SilverCfg
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{Term, Var}
import viper.silicon.supporters.PredicateData
import viper.silicon.supporters.functions.{FunctionData, FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.{Map, Stack}

final case class State(g: Store = Store(),
                       h: Heap = Heap(),
                       program: ast.Program,
                       predicateData: Map[ast.Predicate, PredicateData],
                       functionData: Map[ast.Function, FunctionData],
                       oldHeaps: OldHeaps = Map.empty,

                       parallelizeBranches: Boolean = false,

                       recordVisited: Boolean = false,
                       visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */

                       methodCfg: SilverCfg = null,
                       invariantContexts: Stack[Heap] = Stack.empty,

                       constrainableARPs: InsertionOrderedSet[Var] = InsertionOrderedSet.empty,
                       quantifiedVariables: Stack[Var] = Nil,
                       retrying: Boolean = false,
                       underJoin: Boolean = false,
                       functionRecorder: FunctionRecorder = NoopFunctionRecorder,
                       conservingSnapshotGeneration: Boolean = false,
                       recordPossibleTriggers: Boolean = false,
                       possibleTriggers: Map[ast.Exp, Term] = Map(),

                       triggerExp: Boolean = false,

                       partiallyConsumedHeap: Option[Heap] = None,
                       permissionScalingFactor: Term = terms.FullPerm(),

                       reserveHeaps: Stack[Heap] = Nil,
                       reserveCfgs: Stack[SilverCfg] = Stack(),
                       conservedPcs: Stack[Vector[RecordedPathConditions]] = Stack(),
                       recordPcs: Boolean = false,
                       exhaleExt: Boolean = false,

                       ssCache: SsCache = Map.empty,
                       hackIssue387DisablePermissionConsumption: Boolean = false,

                       qpFields: InsertionOrderedSet[ast.Field] = InsertionOrderedSet.empty,
                       qpPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty,
                       qpMagicWands: InsertionOrderedSet[MagicWandIdentifier] = InsertionOrderedSet.empty,
                       smCache: SnapshotMapCache = SnapshotMapCache.empty,
                       pmCache: PmCache = Map.empty,
                       smDomainNeeded: Boolean = false,
                       /* TODO: Isn't this data stable, i.e. fully known after a preprocessing step? If so, move it to the appropriate supporter. */
                       predicateSnapMap: Map[ast.Predicate, terms.Sort] = Map.empty,
                       predicateFormalVarMap: Map[ast.Predicate, Seq[terms.Var]] = Map.empty,
                       isMethodVerification: Boolean = false,
                       retryLevel: Int = 0,
                       /* ast.Field, ast.Predicate, or MagicWandIdentifier */
                       heapDependentTriggers: InsertionOrderedSet[Any] = InsertionOrderedSet.empty,
                       moreCompleteExhale: Boolean = false)
    extends Mergeable[State] {

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

  def setConstrainable(arps: Iterable[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

  def scalePermissionFactor(p: Term) =
    copy(permissionScalingFactor = terms.PermTimes(p, permissionScalingFactor))

  def merge(other: State): State =
    State.merge(this, other)

  def preserveAfterLocalEvaluation(post: State): State =
    State.preserveAfterLocalEvaluation(this, post)

  def functionRecorderQuantifiedVariables(): Seq[Var] =
    functionRecorder.data.fold(Seq.empty[Var])(_.arguments)

  def relevantQuantifiedVariables(filterPredicate: Var => Boolean): Seq[Var] = (
       functionRecorderQuantifiedVariables()
    ++ quantifiedVariables.filter(filterPredicate)
  )

  def relevantQuantifiedVariables(occurringIn: Seq[Term]): Seq[Var] =
    relevantQuantifiedVariables(x => occurringIn.exists(_.contains(x)))

  lazy val relevantQuantifiedVariables: Seq[Var] =
    relevantQuantifiedVariables(_ => true)

  override val toString = s"${this.getClass.getSimpleName}(...)"
}

object State {
  type OldHeaps = Map[String, Heap]
  val OldHeaps = Map

  def merge(s1: State, s2: State): State = {
    s1 match {
      /* Decompose state s1 */
      case State(g1, h1, program,
                 predicateData,
                 functionData,
                 oldHeaps1,
                 parallelizeBranches1,
                 recordVisited1, visited1,
                 methodCfg1, invariantContexts1,
                 constrainableARPs1,
                 quantifiedVariables1,
                 retrying1,
                 underJoin1,
                 functionRecorder1,
                 conservingSnapshotGeneration1,
                 recordPossibleTriggers1, possibleTriggers1,
                 triggerExp1,
                 partiallyConsumedHeap1,
                 permissionScalingFactor1,
                 reserveHeaps1, reserveCfgs1, conservedPcs1, recordPcs1, exhaleExt1,
                 ssCache1, hackIssue387DisablePermissionConsumption1,
                 qpFields1, qpPredicates1, qpMagicWands1, smCache1, pmCache1, smDomainNeeded1,
                 predicateSnapMap1, predicateFormalVarMap1, hack, retryLevel, useHeapTriggers,
                 moreCompleteExhale) =>

        /* Decompose state s2: most values must match those of s1 */
        s2 match {
          case State(`g1`, `h1`,
                     `program`,
                     `predicateData`, `functionData`,
                     `oldHeaps1`,
                     `parallelizeBranches1`,
                     `recordVisited1`, `visited1`,
                     `methodCfg1`, `invariantContexts1`,
                     constrainableARPs2,
                     `quantifiedVariables1`,
                     `retrying1`,
                     `underJoin1`,
                     functionRecorder2,
                     `conservingSnapshotGeneration1`,
                     `recordPossibleTriggers1`, possibleTriggers2,
                     triggerExp2,
                     `partiallyConsumedHeap1`,
                     `permissionScalingFactor1`,
                     `reserveHeaps1`, `reserveCfgs1`, `conservedPcs1`, `recordPcs1`, `exhaleExt1`,
                     ssCache2, `hackIssue387DisablePermissionConsumption1`,
                     `qpFields1`, `qpPredicates1`, `qpMagicWands1`, smCache2, pmCache2, `smDomainNeeded1`,
                     `predicateSnapMap1`, `predicateFormalVarMap1`, `hack`, `retryLevel`, `useHeapTriggers`,
                     moreCompleteExhale2) =>

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            val smCache3 = smCache1.union(smCache2)
            val pmCache3 = pmCache1 ++ pmCache2

            val ssCache3 = ssCache1 ++ ssCache2
            val moreCompleteExhale3 = moreCompleteExhale || moreCompleteExhale2

            s1.copy(functionRecorder = functionRecorder3,
                    possibleTriggers = possibleTriggers3,
                    triggerExp = triggerExp3,
                    constrainableARPs = constrainableARPs3,
                    ssCache = ssCache3,
                    smCache = smCache3,
                    pmCache = pmCache3,
                    moreCompleteExhale = moreCompleteExhale3)

          case _ =>
            val err = new StringBuilder()
            for (ix <- 0 until s1.productArity) {
              val e1 = s1.productElement(ix)
              val e2 = s2.productElement(ix)
              if (e1 != e2) {
                err ++= s"\n- Field index ${s1.productElementName(ix)} not equal."
              }
            }
            sys.error(s"State merging failed: unexpected mismatch between symbolic states: $err")
      }
    }
  }

  def preserveAfterLocalEvaluation(pre: State, post: State): State = {
    pre.copy(functionRecorder = post.functionRecorder,
             possibleTriggers = post.possibleTriggers,
             smCache = post.smCache,
             constrainableARPs = post.constrainableARPs)
  }

  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K,V] =
    viper.silicon.utils.conflictFreeUnion(m1, m2) match {
      case (m3, conflicts) if conflicts.isEmpty => m3
      case _ => sys.error("Unexpected mismatch between contexts")
    }

  def merge[M <: Mergeable[M]](candidate1: Option[M], candidate2: Option[M]): Option[M] =
    (candidate1, candidate2) match {
      case (Some(m1), Some(m2)) => Some(m1.merge(m2))
      case (None, None) => None
      case _ => sys.error("Unexpected mismatch between contexts")
    }
}
