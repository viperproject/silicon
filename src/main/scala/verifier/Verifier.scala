// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import com.typesafe.scalalogging.Logger
import viper.silicon.{Config, Map}
import viper.silicon.decider.{Decider, PathConditionStack}
import viper.silicon.logger.MemberSymbExLogger
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.terms.{AxiomRewriter, Term, TriggerGenerator}
import viper.silicon.rules.{HeapSupportRules, StateConsolidationRules}
import viper.silicon.state.{Heap, IdentifierFactory, State, SymbolConverter}
import viper.silicon.supporters.{QuantifierSupporter, SnapshotSupporter}
import viper.silicon.utils.Counter
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

  val heapSupporter: HeapSupportRules

  def verificationPoolManager: VerificationPoolManager

  val errorsReportedSoFar = new AtomicInteger(0);

  private lazy val heapRecorder = new DebugHeapRecorder()

  def getDebugOldLabel(s: State, pos: ast.Position, h: Option[Heap] = None): String =
    heapRecorder.getDebugOldLabel(s, pos, h)
  def getDebugHeapLabel(s: State, h: Option[Heap] = None): Option[String] =
    heapRecorder.getDebugHeapLabel(s, h)
  def recordHeap(s: State, parentLabel: String, cause: HeapCause, oldPCS: PathConditionStack): State =
    heapRecorder.recordHeap(s, None, parentLabel, cause, oldPCS, decider.pcs.duplicate())
  def recordHeap(s: State, currentLabel: String, parentLabel: String, cause: HeapCause, oldPCS: PathConditionStack): State =
    heapRecorder.recordHeap(s, Some(currentLabel), parentLabel, cause, oldPCS, decider.pcs.duplicate())
  def startKeyHeap(s: State, parentLabel: String, cause: HeapCause): State =
    heapRecorder.startKeyHeap(s, parentLabel, cause, decider.pcs.duplicate())
  def recordIntermediateHeap(s: State): State =
    heapRecorder.recordIntermediateHeap(s, decider.pcs.duplicate(), None)
  def recordIntermediateHeap(s: State, cause: HeapCause): State =
    heapRecorder.recordIntermediateHeap(s, decider.pcs.duplicate(), Some(cause))
  def finishKeyHeap(s: State): State =
    heapRecorder.finishKeyHeap(s, decider.pcs.duplicate())

  def reportFurtherErrors(): Boolean = (Verifier.config.numberOfErrorsToReport() > errorsReportedSoFar.get()
    || Verifier.config.numberOfErrorsToReport() == 0);
}

object Verifier {
  val PRE_STATE_LABEL = "old"
  val MAGIC_WAND_LHS_STATE_LABEL = ast.LabelledOld.LhsOldLabel

  private var _config: Config = _
  def config: Config = _config
  /*private*/ def config_=(config: Config): Unit = { _config = config }
}

trait VerifierComponent { this: Verifier => }

class DebugHeapRecorder {
  private val debugHeapCounter = new AtomicInteger(0);

  // Returns Left for an existing label or Right when it made a new label.
  private def getOrMakeHeapLabel(s: State, h: Option[Heap]): Either[String, String] = {
    getDebugHeapLabel(s, h) match {
      case Some(label) => Left(label)
      case None =>
        val counter = debugHeapCounter.getAndIncrement()
        Right(s"debug@$counter")
    }
  }

  /**
   * Returns debug label for the current expression in the given heap.
   * @param s the current state
   * @param pos the position of the current expression
   * @param h the heap to consider, if not the heap from state s
   */
  def getDebugOldLabel(s: State, pos: ast.Position, h: Option[Heap]): String = {
    val posString = pos match {
      case column: ast.HasLineColumn => s"l:${column.line}.${column.column}"
      case _ => s"l:unknown"
    }
    val heapLabel = getDebugHeapLabel(s, h).getOrElse("unrecordedHeap")
    s"$heapLabel#$posString"
  }

  /**
  * Returns the label for a given heap, or None if the heap has not been recorded.
  * In case of multiple matches, prefer labelled key heaps then debug key heaps, then tempHeaps, then childrenHeaps.
  */
  def getDebugHeapLabel(s: State, h: Option[Heap]): Option[String] = {
    val heap = h match {
      case Some(heap) => heap
      case None => magicWandSupporter.getEvalHeap(s)
    }

    val equalKeyHeaps = s.debugOldHeaps.collect {
      case (label, record) if heap.equalChunks(record.heap) => label }
    val (debugs, labelled) = equalKeyHeaps.partition(_.contains("debug"))

    if (labelled.nonEmpty) labelled.lastOption
    else if (debugs.nonEmpty) debugs.lastOption
    else {
      val equalChildHeaps = s.debugOldHeaps.view.flatMap(kv => kv._2.intermediateHeaps.collect {
        case (label, record) if heap.equalChunks(record.heap) => label
      }).to(Seq)
      val equalTempHeaps = s.temporaryHeapRecord match {
        case Some((_, _, _, heaps)) => heaps.collect { case (label, record) if heap.equalChunks(record.heap) => label }
        case None => Seq()
      }
      (equalChildHeaps ++ equalTempHeaps).headOption
    }
  }

  private def branchCondDiff(oldPCS: PathConditionStack, newPCS: PathConditionStack): Seq[(ast.Exp, Term)] = {
    val oldBranchConds = oldPCS.branchConditionExps.map(bc => bc._1).zip(oldPCS.branchConditions)
    val currentBranchConds = newPCS.branchConditionExps.map(bc => bc._1).zip(newPCS.branchConditions)
    currentBranchConds.filterNot(oldBranchConds.contains(_))
  }

  // Record a heap as a key heap with no intermediates
  def recordHeap(s: State, currentLabel: Option[String], parentLabel: String, cause: HeapCause,
                 oldPCS: PathConditionStack, newPCS: PathConditionStack): State = {
    lazy val branchConds = branchCondDiff(oldPCS, newPCS)
    lazy val heapRecord = HeapRecord(magicWandSupporter.getEvalHeap(s), parentLabel, cause, branchConds, Map.empty)

    currentLabel match {
      case Some(label) => s.copy(debugOldHeaps = s.debugOldHeaps + (label -> heapRecord))
      case None =>
        getOrMakeHeapLabel(s, None) match {
          case Left(_) => s // Don't overwrite existing label
          case Right(newLabel) => s.copy(debugOldHeaps = s.debugOldHeaps + (newLabel -> heapRecord))
        }
    }
  }

  def startKeyHeap(s: State, parentLabel: String, cause: HeapCause, pcs: PathConditionStack): State = {
    s.copy(temporaryHeapRecord = Some(parentLabel, cause, pcs, Map.empty))
  }

  def recordIntermediateHeap(s: State, newPCS: PathConditionStack, cause: Option[HeapCause]): State = {
    assert(s.isRecordingHeaps, "recordIntermediateHeap called but no temporaryHeapRecord")
    getOrMakeHeapLabel(s, None) match {
      case Left(_) => s
      case Right(newLabel) =>
        val h = magicWandSupporter.getEvalHeap(s)
        val (parentLabel, parentCause, oldPCS, interHeaps) = s.temporaryHeapRecord.get
        val newInterHeap = IntermediateHeapRecord(h, cause, branchCondDiff(oldPCS, newPCS))
        val newTemp = (parentLabel, parentCause, oldPCS, interHeaps + (newLabel -> newInterHeap))
        s.copy(temporaryHeapRecord = Some(newTemp))
    }
  }

  def finishKeyHeap(s: State, newPCS: PathConditionStack): State = {
    assert(s.isRecordingHeaps, "finishKeyHeap called but no temporaryHeapRecord")
    val (parentLabel, cause, oldPCS, interHeaps) = s.temporaryHeapRecord.get
    val h = magicWandSupporter.getEvalHeap(s)

    getOrMakeHeapLabel(s, None) match {
      case Left(existingLabel) =>
        if (interHeaps contains existingLabel) {
          // If the current heap is in the temporary record, promote it to a key heap
          val keyHeap = HeapRecord(h, parentLabel, cause, branchCondDiff(oldPCS, newPCS), interHeaps - existingLabel)
          s.copy(debugOldHeaps = s.debugOldHeaps + (existingLabel -> keyHeap), temporaryHeapRecord = None)
        } else if (s.debugOldHeaps contains existingLabel) {
          // The current heap is an existing heap, so add any new children to that heap
          val existingRecord = s.debugOldHeaps(existingLabel)
          val updatedRecord = existingRecord.copy(intermediateHeaps = existingRecord.intermediateHeaps ++ interHeaps)
          s.copy(debugOldHeaps = s.debugOldHeaps + (existingLabel -> updatedRecord), temporaryHeapRecord = None)
        } else {
          // If the current heap is only recorded as a child, just record it again as a key heap
          val keyHeap = HeapRecord(h, parentLabel, cause, branchCondDiff(oldPCS, newPCS), interHeaps)
          s.copy(debugOldHeaps = s.debugOldHeaps + (existingLabel -> keyHeap), temporaryHeapRecord = None)
        }
      case Right(newLabel) =>
        val keyHeap = HeapRecord(h, parentLabel, cause, branchCondDiff(oldPCS, newPCS), interHeaps)
        s.copy(debugOldHeaps = s.debugOldHeaps + (newLabel -> keyHeap), temporaryHeapRecord = None)
    }
  }
}