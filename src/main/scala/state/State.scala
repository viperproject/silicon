// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silicon.Config.JoinMode
import viper.silicon.Config.JoinMode.JoinMode
import viper.silver.ast
import viper.silver.cfg.silver.SilverCfg
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces.state.GeneralChunk
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{Term, Var}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state.terms.{And, Ite}
import viper.silicon.supporters.PredicateData
import viper.silicon.supporters.functions.{FunctionData, FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier
import viper.silicon.{Map, Stack}
import viper.silver.utility.Sanitizer

// Typed representation of resources that appear as heap-dependent SMT triggers.
// Replaces the previous InsertionOrderedSet[Any] which held ast.Field, ast.Predicate,
// or MagicWandIdentifier values untyped.
// Subtypes are nested to avoid name clash with viper.silicon.state.terms.{FieldTrigger, PredicateTrigger}.
sealed trait HeapDependentTrigger
object HeapDependentTrigger {
  case class Field(field: ast.Field) extends HeapDependentTrigger
  case class Predicate(predicate: ast.Predicate) extends HeapDependentTrigger
  case class Wand(id: MagicWandIdentifier) extends HeapDependentTrigger
}

// Data that is fully determined when a member verification starts and never
// changes during symbolic execution of that member.
case class MemberContext(
  program:               ast.Program,
  currentMember:         Option[ast.Member],
  methodCfg:             SilverCfg = null,
  predicateData:         Map[String, PredicateData],
  functionData:          Map[String, FunctionData],
  predicateSnapMap:      Map[String, terms.Sort] = Map.empty,
  predicateFormalVarMap: Map[String, Seq[terms.Var]] = Map.empty,
  qpFields:              InsertionOrderedSet[ast.Field] = InsertionOrderedSet.empty,
  qpPredicates:          InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty,
  qpMagicWands:          InsertionOrderedSet[MagicWandIdentifier] = InsertionOrderedSet.empty,
  permLocations:         InsertionOrderedSet[ast.Location] = InsertionOrderedSet.empty,
  heapDependentTriggers: InsertionOrderedSet[HeapDependentTrigger] = InsertionOrderedSet.empty
)

// Performance caches whose entries are safe to union across symbolic execution branches.
case class StateCache(
  ssCache:       SsCache = Map.empty,
  smCache:       SnapshotMapCache = SnapshotMapCache.empty,
  pmCache:       PmCache = Map.empty,
  smDomainNeeded: Boolean = false
) {
  def union(other: StateCache): StateCache = StateCache(
    ssCache  ++ other.ssCache,
    smCache.union(other.smCache),
    pmCache  ++ other.pmCache,
    smDomainNeeded || other.smDomainNeeded
  )
}

// Settings that control which symbolic-execution algorithms are used.
// These can be changed during execution (e.g. parallelizeBranches is toggled
// around branch() calls; moreJoins is temporarily set to Off inside function apps).
case class ExecSettings(
  parallelizeBranches:    Boolean  = false,
  moreJoins:              JoinMode = JoinMode.Off,
  moreCompleteExhale:     Boolean  = false,
  assertReadAccessOnly:   Boolean  = false,
  recordPossibleTriggers: Boolean  = false,
  triggerExp:             Boolean  = false
)

// State relevant only during magic-wand package/apply operations.
case class WandPackageContext(
  exhaleExt:    Boolean = false,
  isInPackage:  Boolean = false,
  reserveHeaps: Stack[Heap] = Nil,
  reserveCfgs:  Stack[SilverCfg] = Stack.empty,
  conservedPcs: Stack[Vector[RecordedPathConditions]] = Stack.empty,
  recordPcs:    Boolean = false
)

final case class State(
  g:    Store = Store(),
  h:    Heap = Heap(),
  oldHeaps: OldHeaps = Map.empty,

  mc:    MemberContext,
  cache: StateCache = StateCache(),
  wand:  WandPackageContext = WandPackageContext(),

  settings: ExecSettings = ExecSettings(),

  recordVisited: Boolean = false,
  visited:       List[ast.Predicate] = Nil,

  constrainableARPs:   InsertionOrderedSet[Var] = InsertionOrderedSet.empty,
  quantifiedVariables: Stack[(Var, Option[ast.AbstractLocalVar])] = Nil,

  retrying:   Boolean = false,
  underJoin:  Boolean = false,

  partiallyConsumedHeap: Option[Heap] = None,

  functionRecorder: FunctionRecorder = NoopFunctionRecorder,

  possibleTriggers: Map[ast.Exp, Term] = Map.empty,

  permissionScalingFactor:    Term = terms.FullPerm,
  permissionScalingFactorExp: Option[ast.Exp] = None,

  isEvalInOld:       Boolean = false,
  invariantContexts: Stack[Heap] = Stack.empty,
  retryLevel:        Int = 0
) extends Mergeable[State] {

  // Forwarding accessors for MemberContext fields — call sites need no changes.
  def program:               ast.Program                                   = mc.program
  def currentMember:         Option[ast.Member]                            = mc.currentMember
  def methodCfg:             SilverCfg                                     = mc.methodCfg
  def predicateData:         Map[String, PredicateData]                    = mc.predicateData
  def functionData:          Map[String, FunctionData]                     = mc.functionData
  def predicateSnapMap:      Map[String, terms.Sort]                       = mc.predicateSnapMap
  def predicateFormalVarMap: Map[String, Seq[terms.Var]]                   = mc.predicateFormalVarMap
  def qpFields:              InsertionOrderedSet[ast.Field]                = mc.qpFields
  def qpPredicates:          InsertionOrderedSet[ast.Predicate]            = mc.qpPredicates
  def qpMagicWands:          InsertionOrderedSet[MagicWandIdentifier]      = mc.qpMagicWands
  def permLocations:         InsertionOrderedSet[ast.Location]         = mc.permLocations
  def heapDependentTriggers: InsertionOrderedSet[HeapDependentTrigger] = mc.heapDependentTriggers

  // Forwarding accessors for StateCache fields.
  def ssCache:        SsCache          = cache.ssCache
  def smCache:        SnapshotMapCache = cache.smCache
  def pmCache:        PmCache          = cache.pmCache
  def smDomainNeeded: Boolean          = cache.smDomainNeeded

  // Forwarding accessors for WandPackageContext fields.
  def exhaleExt:    Boolean      = wand.exhaleExt
  def isInPackage:  Boolean      = wand.isInPackage
  def reserveHeaps: Stack[Heap]  = wand.reserveHeaps
  def reserveCfgs:           Stack[SilverCfg]                   = wand.reserveCfgs
  def conservedPcs:          Stack[Vector[RecordedPathConditions]] = wand.conservedPcs
  def recordPcs:             Boolean                            = wand.recordPcs

  // Forwarding accessors for ExecSettings fields.
  def parallelizeBranches:    Boolean  = settings.parallelizeBranches
  def moreJoins:              JoinMode = settings.moreJoins
  def moreCompleteExhale:     Boolean  = settings.moreCompleteExhale
  def assertReadAccessOnly:   Boolean  = settings.assertReadAccessOnly
  def recordPossibleTriggers: Boolean  = settings.recordPossibleTriggers
  def triggerExp:             Boolean  = settings.triggerExp

  // Helpers for updating sub-objects without deeply nested copy() at call sites.
  def updateMc(f: MemberContext => MemberContext): State          = copy(mc       = f(mc))
  def updateCache(f: StateCache => StateCache): State             = copy(cache    = f(cache))
  def updateWand(f: WandPackageContext => WandPackageContext): State = copy(wand  = f(wand))
  def updateSettings(f: ExecSettings => ExecSettings): State      = copy(settings = f(settings))

  val isMethodVerification: Boolean =
    currentMember.isEmpty || currentMember.get.isInstanceOf[ast.Method]

  def isUsedAsTrigger(res: ast.Resource): Boolean = {
    val trigger: HeapDependentTrigger = res match {
      case f:  ast.Field    => HeapDependentTrigger.Field(f)
      case p:  ast.Predicate => HeapDependentTrigger.Predicate(p)
      case mw: ast.MagicWand => HeapDependentTrigger.Wand(MagicWandIdentifier(mw, program))
    }
    heapDependentTriggers.contains(trigger)
  }

  def isQuantifiedResource(res: ast.Resource): Boolean = res match {
    case f:  ast.Field    => qpFields.contains(f)
    case p:  ast.Predicate => qpPredicates.contains(p)
    case mw: ast.MagicWand => qpMagicWands.contains(MagicWandIdentifier(mw, program))
  }

  def isPermLocation(res: ast.Resource): Boolean = res match {
    case loc: ast.Location => permLocations.contains(loc)
    case _                 => false
  }

  def getFormalArgVars(res: ast.Resource, v: Verifier): Seq[Var] = res match {
    case _: ast.Field    => Seq(`?r`)
    case p: ast.Predicate => predicateFormalVarMap(p.name)
    case w: ast.MagicWand =>
      val bodyVars = w.subexpressionsToEvaluate(program)
      bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
  }

  def getFormalArgDecls(res: ast.Resource): Seq[ast.LocalVarDecl] = res match {
    case _: ast.Field    => Seq(ast.LocalVarDecl("r", ast.Ref)())
    case p: ast.Predicate => p.formalArgs
    case w: ast.MagicWand =>
      val bodyVars = w.subexpressionsToEvaluate(program)
      bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)())
  }

  val mayAssumeUpperBounds: Boolean =
    currentMember.isEmpty || !currentMember.get.isInstanceOf[ast.Function] || Verifier.config.respectFunctionPrePermAmounts()

  val isLastRetry: Boolean = retryLevel == 0

  def incCycleCounter(m: ast.Predicate) =
    if (recordVisited) copy(visited = m :: visited)
    else this

  def decCycleCounter(m: ast.Member) =
    if (recordVisited) {
      require(visited.contains(m))
      val (ms, others) = visited.partition(_ == m)
      copy(visited = ms.tail ::: others)
    } else this

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Iterable[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps
    copy(constrainableARPs = newConstrainableARPs)
  }

  def scalePermissionFactor(p: Term, exp: Option[ast.Exp]) =
    copy(
      permissionScalingFactor = terms.PermTimes(p, permissionScalingFactor),
      permissionScalingFactorExp = permissionScalingFactorExp.map(psf =>
        ast.PermMul(exp.get, psf)(exp.get.pos, exp.get.info, exp.get.errT)))

  def merge(other: State): State = State.merge(this, other)

  def preserveAfterLocalEvaluation(post: State): State =
    State.preserveAfterLocalEvaluation(this, post)

  def functionRecorderQuantifiedVariables(): Seq[(Var, Option[ast.AbstractLocalVar])] =
    functionRecorder.arguments.fold(Seq.empty[(Var, Option[ast.AbstractLocalVar])])(d => d)

  def relevantQuantifiedVariables(filterPredicate: Var => Boolean): Seq[(Var, Option[ast.AbstractLocalVar])] = (
       functionRecorderQuantifiedVariables()
    ++ quantifiedVariables.filter(x => filterPredicate(x._1))
  )

  def relevantQuantifiedVariables(occurringIn: Seq[Term]): Seq[(Var, Option[ast.AbstractLocalVar])] =
    relevantQuantifiedVariables(x => occurringIn.exists(_.contains(x)))

  def substituteVarsInExp(e: ast.Exp): ast.Exp = {
    val varMapping = g.expValues.map { case (localVar, finalExp) => localVar.name -> finalExp }
    Sanitizer.replaceFreeVariablesInExpression(e, varMapping.map(vm => vm._1 -> vm._2.get), Set())
  }

  lazy val relevantQuantifiedVariables: Seq[(Var, Option[ast.AbstractLocalVar])] =
    relevantQuantifiedVariables(_ => true)

  override val toString = s"${this.getClass.getSimpleName}(...)"
}

object State {
  type OldHeaps = Map[String, Heap]
  val OldHeaps = Map

  def merge(s1: State, s2: State): State = {
    // Fields that must be identical on both branches before a simple (non-PC) merge.
    if (s1.g != s2.g || s1.h != s2.h || s1.mc != s2.mc ||
        s1.parallelizeBranches != s2.parallelizeBranches ||
        s1.recordVisited != s2.recordVisited || s1.visited != s2.visited ||
        s1.invariantContexts != s2.invariantContexts ||
        s1.retrying != s2.retrying || s1.underJoin != s2.underJoin ||
        s1.recordPossibleTriggers != s2.recordPossibleTriggers ||
        s1.wand.exhaleExt != s2.wand.exhaleExt ||
        s1.wand.isInPackage != s2.wand.isInPackage ||
        s1.partiallyConsumedHeap != s2.partiallyConsumedHeap ||
        s1.wand.reserveHeaps != s2.wand.reserveHeaps ||
        s1.wand.reserveCfgs != s2.wand.reserveCfgs ||
        s1.wand.recordPcs != s2.wand.recordPcs ||
        s1.permissionScalingFactor != s2.permissionScalingFactor ||
        s1.permissionScalingFactorExp != s2.permissionScalingFactorExp ||
        s1.isEvalInOld != s2.isEvalInOld ||
        s1.assertReadAccessOnly != s2.assertReadAccessOnly ||
        s1.cache.smDomainNeeded != s2.cache.smDomainNeeded ||
        s1.retryLevel != s2.retryLevel) {
      generateStateMismatchErrorMessage(s1, s2)
    }

    assert(s1.wand.conservedPcs.length == s2.wand.conservedPcs.length)
    val conservedPcs3 = s1.wand.conservedPcs.zip(s2.wand.conservedPcs)
      .map { case (pcs1, pcs2) => (pcs1 ++ pcs2).distinct }

    s1.copy(
      oldHeaps            = s1.oldHeaps ++ s2.oldHeaps,
      cache               = s1.cache.union(s2.cache),
      wand                = s1.wand.copy(conservedPcs = conservedPcs3),
      functionRecorder    = s1.functionRecorder.merge(s2.functionRecorder),
      possibleTriggers    = s1.possibleTriggers ++ s2.possibleTriggers,
      constrainableARPs   = s1.constrainableARPs ++ s2.constrainableARPs,
      quantifiedVariables = (s1.quantifiedVariables ++ s2.quantifiedVariables).distinct
    ).updateSettings(_.copy(
        moreCompleteExhale = s1.moreCompleteExhale || s2.moreCompleteExhale,
        triggerExp         = s1.triggerExp && s2.triggerExp))
  }

  private def generateStateMismatchErrorMessage(s1: State, s2: State): Nothing = {
    val err = new StringBuilder()
    for (ix <- 0 until s1.productArity) {
      val e1 = s1.productElement(ix)
      val e2 = s2.productElement(ix)
      if (e1 != e2) {
        err ++= s"\n\tField ${s1.productElementName(ix)} not equal"
        err ++= s"\n\t\t state1: $e1"
        err ++= s"\n\t\t state2: $e2"
      }
    }
    sys.error(s"State merging failed: unexpected mismatch between symbolic states: $err")
  }

  private def mergeMaps[K, V, D](map1: Map[K, V], data1: D, map2: Map[K, V], data2: D)
                                (fOnce: (V, D) => Option[V])
                                (fTwice: (V, D, V, D) => Option[V])
                                : Map[K, V] = {
    map1.flatMap { case (k, v1) =>
      (map2.get(k) match {
        case Some(v2) => fTwice(v1, data1, v2, data2)
        case None     => fOnce(v1, data1)
      }).map(v => (k, v))
    } ++ map2.flatMap { case (k, v2) =>
      (map1.get(k) match {
        case Some(_) => None
        case None    => fOnce(v2, data2)
      }).map(v => (k, v))
    }
  }

  private def conditionalizeChunks(h: Iterable[Chunk], cond: Term, condExp: Option[ast.Exp]): Iterable[Chunk] =
    h map {
      case c: GeneralChunk => c.applyCondition(cond, condExp)
      case _               => sys.error("Chunk type not conditionalizable.")
    }

  private def conditionalizeHeap(h: Heap, cond: Term, condExp: Option[ast.Exp]): Heap =
    Heap(conditionalizeChunks(h.values, cond, condExp))

  def mergeHeap(h1: Heap, cond1: Term, cond1Exp: Option[ast.Exp],
                h2: Heap, cond2: Term, cond2Exp: Option[ast.Exp]): Heap = {
    val (unconditional, h1ToConditionalize) = h1.values.partition(c1 => h2.values.exists(_ == c1))
    val h2ToConditionalize = h2.values.filter(c2 => !unconditional.exists(_ == c2))
    Heap(unconditional) +
      Heap(conditionalizeChunks(h1ToConditionalize, cond1, cond1Exp)) +
      Heap(conditionalizeChunks(h2ToConditionalize, cond2, cond2Exp))
  }

  def merge(s1: State, pc1: RecordedPathConditions, s2: State, pc2: RecordedPathConditions): State = {
    // Fields that must be identical on both branches before a PC-aware merge.
    if (s1.mc != s2.mc ||
        s1.parallelizeBranches != s2.parallelizeBranches ||
        s1.recordVisited != s2.recordVisited || s1.visited != s2.visited ||
        s1.quantifiedVariables != s2.quantifiedVariables ||
        s1.retrying != s2.retrying || s1.underJoin != s2.underJoin ||
        s1.recordPossibleTriggers != s2.recordPossibleTriggers ||
        s1.permissionScalingFactor != s2.permissionScalingFactor ||
        s1.permissionScalingFactorExp != s2.permissionScalingFactorExp ||
        s1.isEvalInOld != s2.isEvalInOld ||
        s1.wand.reserveCfgs != s2.wand.reserveCfgs ||
        s1.wand.recordPcs != s2.wand.recordPcs ||
        s1.wand.exhaleExt != s2.wand.exhaleExt ||
        s1.wand.isInPackage != s2.wand.isInPackage ||
        s1.assertReadAccessOnly != s2.assertReadAccessOnly ||
        s1.retryLevel != s2.retryLevel) {
      generateStateMismatchErrorMessage(s1, s2)
    }

    val withExp    = Verifier.config.enableDebugging()
    val cond1      = And(pc1.branchConditions)
    val cond1Exp   = Option.when(withExp)(BigAnd(pc1.branchConditionExps.map(_._2.get)))
    val cond2      = And(pc2.branchConditions)
    val cond2Exp   = Option.when(withExp)(BigAnd(pc2.branchConditionExps.map(_._2.get)))

    val g3 = Store(mergeMaps(s1.g.values, (cond1, cond1Exp), s2.g.values, (cond2, cond2Exp))
      ((_, _) => None)
      ((v1, c1, v2, _) =>
        if (v1._1 == v2._1) Some(v1)
        else {
          assert(v1._1.sort == v2._1.sort)
          Some((Ite(c1._1, v1._1, v2._1), c1._2.map(c => ast.CondExp(c, v1._2.get, v2._2.get)())))
        }))

    val h3 = mergeHeap(s1.h, cond1, cond1Exp, s2.h, cond2, cond2Exp)

    val partiallyConsumedHeap3 = (s1.partiallyConsumedHeap, s2.partiallyConsumedHeap) match {
      case (None,       None)       => None
      case (Some(pch1), None)       => Some(conditionalizeHeap(pch1, cond1, cond1Exp))
      case (None,       Some(pch2)) => Some(conditionalizeHeap(pch2, cond2, cond2Exp))
      case (Some(pch1), Some(pch2)) => Some(mergeHeap(pch1, cond1, cond1Exp, pch2, cond2, cond2Exp))
    }

    val oldHeaps3 = Map.from(
      mergeMaps(s1.oldHeaps, (cond1, cond1Exp), s2.oldHeaps, (cond2, cond2Exp))
        ((_, _) => None)
        ((heap1, c1, heap2, c2) => Some(mergeHeap(heap1, c1._1, c1._2, heap2, c2._1, c2._2))))

    assert(s1.invariantContexts.length == s2.invariantContexts.length)
    val invariantContexts3 = s1.invariantContexts.zip(s2.invariantContexts)
      .map { case (ih1, ih2) => mergeHeap(ih1, cond1, cond1Exp, ih2, cond2, cond2Exp) }

    assert(s1.wand.reserveHeaps.length == s2.wand.reserveHeaps.length)
    val reserveHeaps3 = s1.wand.reserveHeaps.zip(s2.wand.reserveHeaps)
      .map { case (rh1, rh2) => mergeHeap(rh1, cond1, cond1Exp, rh2, cond2, cond2Exp) }

    assert(s1.wand.conservedPcs.length == s2.wand.conservedPcs.length)
    val conservedPcs3 = s1.wand.conservedPcs.zip(s2.wand.conservedPcs)
      .map { case (pcs1, pcs2) => (pcs1 ++ pcs2).distinct }

    s1.copy(
      g             = g3,
      h             = h3,
      oldHeaps      = oldHeaps3,
      invariantContexts      = invariantContexts3,
      cache                  = s1.cache.union(s2.cache),
      partiallyConsumedHeap  = partiallyConsumedHeap3,
      wand          = s1.wand.copy(
                        reserveHeaps = reserveHeaps3,
                        conservedPcs = conservedPcs3),
      constrainableARPs   = s1.constrainableARPs ++ s2.constrainableARPs,
      functionRecorder    = s1.functionRecorder.merge(s2.functionRecorder),
      possibleTriggers    = s1.possibleTriggers ++ s2.possibleTriggers
    ).updateSettings(_.copy(
        moreCompleteExhale = s1.moreCompleteExhale || s2.moreCompleteExhale,
        triggerExp         = s1.triggerExp && s2.triggerExp))
  }

  def preserveAfterLocalEvaluation(pre: State, post: State): State =
    pre.copy(
      functionRecorder  = post.functionRecorder,
      possibleTriggers  = post.possibleTriggers,
      cache             = post.cache,
      constrainableARPs = post.constrainableARPs)

  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K, V] =
    viper.silicon.utils.conflictFreeUnion(m1, m2) match {
      case (m3, conflicts) if conflicts.isEmpty => m3
      case _ => sys.error("Unexpected mismatch between contexts")
    }

  def merge[M <: Mergeable[M]](candidate1: Option[M], candidate2: Option[M]): Option[M] =
    (candidate1, candidate2) match {
      case (Some(m1), Some(m2)) => Some(m1.merge(m2))
      case (None, None)         => None
      case _                    => sys.error("Unexpected mismatch between contexts")
    }
}
