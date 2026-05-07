// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import com.typesafe.scalalogging.Logger
import viper.silicon.decider.Decider
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.terms.{AxiomRewriter, Term, TriggerGenerator}
import viper.silicon.rules.{HeapSupportRules, StateConsolidationRules, defaultHeapSupporter, magicWandSupporter}
import viper.silicon.state.{Heap, HeapParent, IdentifierFactory, State, SymbolConverter}
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
      case None => s.h
    }
    val equalHeaps = s.oldHeaps.filter(h => (h._1.startsWith("debug@") || h._1.equals("old")) && h._2.equals(heap)).keys
    if (equalHeaps.nonEmpty){
      equalHeaps.head
    } else {
      val counter = debugHeapCounter.getAndIncrement()
      s"debug@$counter"
    }
  }

  def recordOldHeap(s: State, parent: Heap, cause: ast.Stmt): State = {
    recordOldHeap(s, magicWandSupporter.getEvalHeap(s), parent, Left(cause), None)
  }

  def recordOldHeap(s: State, parent: Heap, cause: ast.Stmt, branch: Term): State = {
    recordOldHeap(s, magicWandSupporter.getEvalHeap(s), parent, Left(cause), Some(branch))
  }

  def recordOldHeap(s: State, parent: Heap, cause: ast.Exp): State = {
    recordOldHeap(s, magicWandSupporter.getEvalHeap(s), parent, Right(cause), None)
  }

  def recordOldHeap(s: State, parent: Heap, cause: ast.Exp, branch: Term): State = {
    recordOldHeap(s, magicWandSupporter.getEvalHeap(s), parent, Right(cause), Some(branch))
  }

  def recordOldHeap(s: State, heap: Heap, parent: Heap, cause: Either[ast.Stmt, ast.Exp], branch: Option[Term]): State = {
    val childLabel = getDebugHeapLabel(s, Some(heap))
    val oldHeapParents2 = if (s.oldHeapParents.contains(childLabel))
      s.oldHeapParents
    else {
      val parentLabel = getDebugHeapLabel(s, Some(parent))
      val heapParent = HeapParent(parentLabel, cause, branch)
      s.oldHeapParents + (childLabel -> heapParent)
    }

    s.copy(oldHeaps = s.oldHeaps + (childLabel -> heap), oldHeapParents = oldHeapParents2)
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
