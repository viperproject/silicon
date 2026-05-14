// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import com.typesafe.scalalogging.Logger
import viper.silicon.decider.{Decider, PathConditionStack}
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.terms.{AxiomRewriter, Term, TriggerGenerator}
import viper.silicon.rules.{HeapSupportRules, StateConsolidationRules, defaultHeapSupporter, magicWandSupporter}
import viper.silicon.state.{DebugHeap, EvalExp, ExecStmt, Heap, HeapCause, IdentifierFactory, State, SymbolConverter}
import viper.silicon.supporters.{QuantifierSupporter, SnapshotSupporter}
import viper.silicon.utils.Counter
import viper.silicon.Config
import viper.silicon.logger.MemberSymbExLogger
import viper.silver.ast
import viper.silver.reporter.Reporter

import java.util.concurrent.atomic.AtomicInteger

trait Verifier {
  def uniqueId: String

  def symbExLog: MemberSymbExLogger
  def openSymbExLogger(member: ast.Member): Unit
  def logger: Logger
  def reporter: Reporter
  def counter(id: AnyRef): Counter

  def decider: Decider
  def symbolConverter: SymbolConverter
  def stateFormatter: StateFormatter
  def identifierFactory: IdentifierFactory
  def triggerGenerator: TriggerGenerator
  def axiomRewriter: AxiomRewriter
  def quantifierSupporter: QuantifierSupporter
  def snapshotSupporter: SnapshotSupporter
  def stateConsolidator(s: State): StateConsolidationRules

  val heapSupporter: HeapSupportRules = defaultHeapSupporter

  def verificationPoolManager: VerificationPoolManager

  val errorsReportedSoFar = new AtomicInteger(0);

  private val debugHeapCounter = new AtomicInteger(0);

  def reportFurtherErrors(): Boolean = (Verifier.config.numberOfErrorsToReport() > errorsReportedSoFar.get()
    || Verifier.config.numberOfErrorsToReport() == 0);

  /**
    * Returns debug labels for 1) the given heap (will reuse an existing one if one already exists), independently of
    * the position of the current expression, and 2) the current expression in the given heap.
    * @param s the current state
    * @param pos the position of the current expression
    * @param h the heap to consider, if not the heap from state s
    * @return a pair containing the label of the given heap, and the label of the current expression in the given heap
    */
  def getDebugOldLabel(s: State, pos: ast.Position, h: Option[Heap] = None): (String, String) = {
    val posString = pos match {
      case column: ast.HasLineColumn => s"l:${column.line}.${column.column}"
      case _ => s"l:unknown"
    }
    val heapLabel = getDebugHeapLabel(s, h)
    (heapLabel, s"$heapLabel#$posString")
  }

  def getDebugHeapLabel(s: State, h: Option[Heap] = None): String = {
    val heap = h match {
      case Some(heap) => heap
      case None => magicWandSupporter.getEvalHeap(s)
    }
    val equalHeaps = s.debugOldHeaps.filter(dh => dh._2.heap.equals(heap)).keys
    if (equalHeaps.nonEmpty){
      equalHeaps.head
    } else {
      val counter = debugHeapCounter.getAndIncrement()
      s"debug@$counter"
    }
  }

  def recordDebugHeap(s: State, parent: Heap, cause: HeapCause): State = {
    recordDebugHeap(s, magicWandSupporter.getEvalHeap(s), getDebugHeapLabel(s, Some(parent)), cause, None, None)
  }

  def recordDebugHeap(s: State, parent: Heap, cause: HeapCause, oldPCS: PathConditionStack): State = {
    recordDebugHeap(s, magicWandSupporter.getEvalHeap(s), getDebugHeapLabel(s, Some(parent)), cause, None, Some(oldPCS))
  }

  def recordDebugHeap(s: State, parentLabel: String, cause: HeapCause, oldPCS: PathConditionStack): State = {
    recordDebugHeap(s, magicWandSupporter.getEvalHeap(s), parentLabel, cause, None, Some(oldPCS))
  }

  def recordDebugHeap(s: State, parentLabel: String, cause: HeapCause,
                      intermediateCause: ast.Exp, oldPCS: PathConditionStack): State = {
    recordDebugHeap(s, magicWandSupporter.getEvalHeap(s), parentLabel, cause, Some(intermediateCause), Some(oldPCS))
  }

  def recordDebugHeap(s: State, heap: Heap, parentLabel: String,
                      cause: HeapCause,
                      intermediateCause: Option[ast.Exp],
                      oldPCS: Option[PathConditionStack]): State = {
    val heapLabel = getDebugHeapLabel(s, Some(heap))
    if (s.debugOldHeaps.contains(heapLabel))
      s // Don't overwrite parents if we return to a heap
    else {
      val newBranchConds = oldPCS match {
        case None => Seq()
        case Some(pcs) =>
          def zipConds(pcs2: PathConditionStack): Seq[(ast.Exp, Term)] =
            pcs2.branchConditionExps.map(bc => bc._1).zip(pcs2.branchConditions)
          val currentBranchConds = zipConds(decider.pcs)
          val oldBranchConds = zipConds(pcs)
          currentBranchConds.filterNot(oldBranchConds.contains(_))
      }
      val debugHeap = DebugHeap(heap, parentLabel, cause, intermediateCause, newBranchConds)
      s.copy(debugOldHeaps = s.debugOldHeaps + (heapLabel -> debugHeap))
    }
  }
}

object Verifier {
  val PRE_STATE_LABEL = "old"
  val MAGIC_WAND_LHS_STATE_LABEL = ast.LabelledOld.LhsOldLabel

  private var _config: Config = _
  def config: Config = _config
  /*private*/ def config_=(config: Config): Unit = { _config = config }
}

trait VerifierComponent { this: Verifier => }
