// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.logger

import org.slf4j.LoggerFactory
import viper.silicon.logger.records.data.DataRecord
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.state.terms
import viper.silver.ast
import viper.silver.reporter.{BranchCondition, Entity, Reporter, VerifierState, VerifierStateFrame, VerifierStateMessage, VerifierStep}

import java.util.concurrent.{Executors, ScheduledExecutorService, TimeUnit}
import scala.collection.mutable
import scala.util.control.NonFatal

/**
  * ================================
  * State reporting (--reportStateAfter)
  * ================================
  * When Silicon spends a long time on a single proof obligation (typically: waiting for the prover to answer a hard
  * query), users get no feedback about what Silicon is doing. This functionality, which is modelled after the
  * corresponding functionality of VerCors' Silicon backend, reports Silicon's current state whenever no new records
  * have been added to a member's symbolic execution log for a configurable amount of time.
  *
  * [[StateReportingMemberSymbExLogger]] is a stackable mixin for [[MemberSymbExLogger]] implementations that keeps
  * track of the data records whose scopes are currently open, together with the branch conditions of the current
  * execution path. [[StateReporter]] is shared by all member logs of a verification run and periodically checks
  * (from a separate daemon thread) whether any of them has not made progress for too long; if so, it reports a
  * [[VerifierStateMessage]] describing the open records, once per period without progress.
  */
class StateReporter(val reporter: Reporter, val reportAfterMillis: Long) {
  require(reportAfterMillis > 0, "reportAfterMillis must be positive")

  private val pollIntervalMillis: Long = (reportAfterMillis / 10).max(50).min(1000)

  private val active = mutable.LinkedHashSet[StateReportingMemberSymbExLogger]()
  private var executor: Option[ScheduledExecutorService] = None
  private var closed = false

  /** Starts monitoring `log`. The polling thread is started lazily when the first log is registered. */
  def register(log: StateReportingMemberSymbExLogger): Unit = synchronized {
    if (closed) return

    active += log

    if (executor.isEmpty) {
      val newExecutor = Executors.newSingleThreadScheduledExecutor((runnable: Runnable) => {
        val thread = new Thread(runnable, "silicon-state-reporter")
        thread.setDaemon(true)
        thread
      })
      newExecutor.scheduleWithFixedDelay(() => poll(), pollIntervalMillis, pollIntervalMillis, TimeUnit.MILLISECONDS)
      executor = Some(newExecutor)
    }
  }

  /** Stops monitoring `log`. The polling thread is stopped when no logs remain. */
  def unregister(log: StateReportingMemberSymbExLogger): Unit = synchronized {
    active -= log
    if (active.isEmpty) stopExecutor()
  }

  def close(): Unit = synchronized {
    closed = true
    active.clear()
    stopExecutor()
  }

  private def stopExecutor(): Unit = {
    executor.foreach(_.shutdownNow())
    executor = None
  }

  private def poll(): Unit = {
    val now = System.currentTimeMillis()
    val logs = synchronized { active.toList }

    logs.foreach(log =>
      try { log.reportStateIfStalled(now) }
      catch { case NonFatal(e) => StateReporter.textLogger.warn(s"Reporting Silicon's current state failed: $e") })
  }
}

object StateReporter {
  private lazy val textLogger = LoggerFactory.getLogger(classOf[StateReporter])

  /** Converts a record into a step of a [[VerifierState]]; multi-line descriptions are cut after the first line. */
  def step(record: DataRecord): VerifierStep = {
    val text = record.toSimpleString
    val firstLine = text.linesIterator.nextOption().getOrElse("")
    val description = if (firstLine.length < text.length) s"$firstLine ..." else firstLine

    VerifierStep(record.toTypeString, Option(record.value), description)
  }
}

/** The branch currently being explored at some branch point. */
sealed trait TakenBranch {
  /** The next branch of the same branch point. */
  def next: TakenBranch
  def condition: BranchCondition
}

object TakenBranch {
  def first(r: BranchingRecord): TakenBranch =
    (r.conditionExp, r.condition) match {
      case (Some(exp), _) => Exp(exp)
      case (None, Some(term)) => Term(term)
      case (None, None) => Alternative(0, r.getBranchInfos.size)
    }

  case class Exp(exp: ast.Exp) extends TakenBranch {
    def next: TakenBranch = Exp(exp match {
      case ast.Not(inner) => inner
      case other => ast.Not(other)(other.pos, other.info)
    })

    def condition: BranchCondition = BranchCondition.Condition(exp)
  }

  case class Term(term: terms.Term) extends TakenBranch {
    def next: TakenBranch = Term(terms.Not(term))
    def condition: BranchCondition = BranchCondition.OpaqueCondition(term.toString)
  }

  /** Branch points without a condition, e.g. the successor edges of a CFG block. */
  case class Alternative(index: Int, count: Int) extends TakenBranch {
    def next: TakenBranch = Alternative(index + 1, count)
    def condition: BranchCondition = BranchCondition.Alternative(index, count)
  }
}

/** Stackable mixin for [[MemberSymbExLogger]] implementations, see [[StateReporter]].
  *
  * Must be mixed into a class that implements the abstract record hooks of [[MemberSymbExLogger]], e.g.
  * [[MemberSymbExLog]] or [[DiscardingMemberSymbExLog]], and must be registered with the [[StateReporter]] after
  * construction.
  */
trait StateReportingMemberSymbExLogger extends MemberSymbExLogger {
  protected def stateReporter: StateReporter

  private val lock = new Object

  /* All of the following fields are guarded by `lock`. */

  /** Records whose scope is currently open, per branch point: the head frame belongs to the innermost branch point,
    * the last frame is the member's root frame. */
  private var openScopeFrames: List[mutable.LinkedHashMap[Int, DataRecord]] = List(mutable.LinkedHashMap())

  /** For each branch point, the records opened in an enclosing frame whose scope was closed while exploring the
    * current branch (since scopes are closed on every branch, such records are still "open" from the perspective of
    * the enclosing frame, but not on the current execution path). */
  private var closedWithinCurrentBranch: List[mutable.Set[Int]] = List(mutable.Set())

  /** Like `closedWithinCurrentBranch`, but accumulated over all branches of each branch point. */
  private var closedWithinAnyBranch: List[mutable.Set[Int]] = List(mutable.Set())

  /** Branches taken on the current execution path, innermost first. */
  private var takenBranches: List[TakenBranch] = Nil

  private var lastProgressMillis: Long = System.currentTimeMillis()
  private var reportedSinceLastProgress: Boolean = false
  private var finished: Boolean = false

  abstract override def appendDataRecord(r: DataRecord): Unit = {
    super.appendDataRecord(r)

    lock.synchronized {
      openScopeFrames.head(r.id) = r
      progressed()
    }
  }

  abstract override def appendScopingRecord(r: ScopingRecord, ignoreBranchingStack: Boolean): Unit = {
    super.appendScopingRecord(r, ignoreBranchingStack)

    r match {
      case close: CloseScopeRecord =>
        val isMemberClose = lock.synchronized {
          if (openScopeFrames.head.contains(close.refId)) {
            openScopeFrames.head.remove(close.refId)
          } else {
            closedWithinCurrentBranch.head += close.refId
            closedWithinAnyBranch.head += close.refId
          }
          progressed()
          main != null && close.refId == main.id
        }
        if (isMemberClose) finish()
      case _: OpenScopeRecord => /* Already accounted for by appendDataRecord */
    }
  }

  abstract override def appendBranchingRecord(r: BranchingRecord): Unit = {
    super.appendBranchingRecord(r)

    lock.synchronized {
      openScopeFrames ::= mutable.LinkedHashMap()
      closedWithinCurrentBranch ::= mutable.Set()
      closedWithinAnyBranch ::= mutable.Set()
      takenBranches ::= TakenBranch.first(r)
      progressed()
    }
  }

  abstract override def doSwitchToNextBranch(uidBranchPoint: Int): Unit = {
    super.doSwitchToNextBranch(uidBranchPoint)

    lock.synchronized {
      openScopeFrames.head.clear()
      closedWithinCurrentBranch.head.clear()
      takenBranches = takenBranches.head.next :: takenBranches.tail
      progressed()
    }
  }

  abstract override def markBranchReachable(uidBranchPoint: Int): Unit = {
    super.markBranchReachable(uidBranchPoint)

    lock.synchronized { progressed() }
  }

  abstract override def doEndBranchPoint(uidBranchPoint: Int): Unit = {
    super.doEndBranchPoint(uidBranchPoint)

    lock.synchronized {
      openScopeFrames = openScopeFrames.tail
      /* Scopes that were closed on some branch are closed for good once all branches have been explored */
      closedWithinAnyBranch.head.foreach(id => openScopeFrames.foreach(_.remove(id)))
      closedWithinCurrentBranch = closedWithinCurrentBranch.tail
      closedWithinAnyBranch = closedWithinAnyBranch.tail
      takenBranches = takenBranches.tail
      progressed()
    }
  }

  override def close(): Unit = {
    super.close()
    finish()
  }

  private def progressed(): Unit = {
    lastProgressMillis = System.currentTimeMillis()
    reportedSinceLastProgress = false
  }

  private def finish(): Unit = {
    lock.synchronized { finished = true }
    stateReporter.unregister(this)
  }

  /** Invoked periodically by the [[StateReporter]]. */
  def reportStateIfStalled(now: Long): Unit = {
    val message = lock.synchronized {
      val stalledFor = now - lastProgressMillis

      if (finished || reportedSinceLastProgress || stalledFor < stateReporter.reportAfterMillis) {
        None
      } else {
        reportedSinceLastProgress = true
        Some(VerifierStateMessage(viper.silicon.Silicon.name, member.asInstanceOf[Entity], stalledFor, currentState()))
      }
    }

    message.foreach(stateReporter.reporter.report)
  }

  /** The currently open records as a [[VerifierState]], outermost frame first. Must be called while holding
    * `lock`. */
  private def currentState(): VerifierState = {
    val notOnCurrentPath = closedWithinCurrentBranch.flatten.toSet
    val frames = openScopeFrames.reverse
    val conditions = None +: takenBranches.reverse.map(branch => Some(branch.condition))

    VerifierState(frames.zip(conditions).map { case (frame, condition) =>
      val steps =
        frame.values.toSeq
          .sortBy(_.id)
          .filterNot(r => notOnCurrentPath.contains(r.id))
          .map(StateReporter.step)

      VerifierStateFrame(condition, steps)
    })
  }
}
