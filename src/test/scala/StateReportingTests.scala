// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import viper.silicon.logger.records.data.ExecuteRecord
import viper.silicon.logger.{StateReporter, StateReportingSymbExLog}
import viper.silicon.state.terms
import viper.silver.ast
import viper.silver.reporter.{BranchCondition, Message, Reporter, VerifierStateMessage}

import java.nio.file.Paths
import scala.collection.mutable.ArrayBuffer

class StateReportingTests extends AnyFunSuite with Matchers {
  private class CollectingReporter extends Reporter {
    val name = "collecting_reporter"
    private val messages = ArrayBuffer[Message]()

    def report(msg: Message): Unit = synchronized { messages += msg }
    def stateMessages: Seq[VerifierStateMessage] = synchronized { messages.toSeq.collect { case m: VerifierStateMessage => m } }
  }

  private def pos(line: Int, column: Int) = ast.SourcePosition(Paths.get("test.vpr"), line, column)

  test("current state is reported once per period without progress") {
    val reporter = new CollectingReporter
    val reportAfterMillis = 300L
    val root = new StateReportingSymbExLog(new StateReporter(reporter, reportAfterMillis))

    val method = ast.Method("m", Seq(), Seq(), Seq(), Seq(), None)(pos(3, 1))
    val outerStmt = ast.Inhale(ast.TrueLit()())(pos(5, 3))
    val condition = ast.LocalVar("b", ast.Bool)(pos(6, 5))
    val innerStmt = ast.Exhale(ast.TrueLit()())(pos(7, 3))

    val log = root.openMemberScope(method, null)
    val outerId = log.openScope(new ExecuteRecord(outerStmt, null, null))
    val branchPoint = log.insertBranchPoint(2, Some(terms.True), Some(condition))
    log.markReachable(branchPoint)
    val innerId = log.openScope(new ExecuteRecord(innerStmt, null, null))

    Thread.sleep(3 * reportAfterMillis)

    val first = reporter.stateMessages
    first should have size 1
    first.head.verifier shouldBe viper.silicon.Silicon.name
    first.head.concerning shouldBe method
    first.head.millisSinceProgress should be >= reportAfterMillis
    first.head.state.render.linesIterator.toSeq shouldBe Seq(
      "method m (3:1)",
      "execute inhale true (5:3)",
      "branch b (6:5):",
      "  execute exhale true (7:3)")

    val frames = first.head.state.frames
    frames should have size 2
    frames(0).branchCondition shouldBe None
    frames(0).steps.map(_.kind) shouldBe Seq("method", "execute")
    frames(0).steps.map(_.node) shouldBe Seq(Some(method), Some(outerStmt))
    frames(1).branchCondition shouldBe Some(BranchCondition.Condition(condition))
    frames(1).steps.map(_.node) shouldBe Seq(Some(innerStmt))

    /* No progress: the state must not be reported again */
    Thread.sleep(3 * reportAfterMillis)
    reporter.stateMessages should have size 1

    /* Progress: the inner statement finishes and the else branch is explored */
    log.closeScope(innerId)
    log.switchToNextBranch(branchPoint)
    log.markReachable(branchPoint)

    Thread.sleep(3 * reportAfterMillis)

    val second = reporter.stateMessages
    second should have size 2
    second(1).state.render.linesIterator.toSeq shouldBe Seq(
      "method m (3:1)",
      "execute inhale true (5:3)",
      "branch !b (6:5):")
    second(1).state.frames(1).branchCondition shouldBe Some(BranchCondition.Condition(ast.Not(condition)()))
    second(1).state.frames(1).steps shouldBe empty

    /* The member finishes: nothing further is reported */
    log.endBranchPoint(branchPoint)
    log.closeScope(outerId)
    log.closeMemberScope()

    Thread.sleep(3 * reportAfterMillis)
    reporter.stateMessages should have size 2

    root.close()
  }

  test("scopes closed on every branch are no longer reported after the branch point") {
    val reporter = new CollectingReporter
    val reportAfterMillis = 300L
    val root = new StateReportingSymbExLog(new StateReporter(reporter, reportAfterMillis))

    val method = ast.Method("m", Seq(), Seq(), Seq(), Seq(), None)(pos(3, 1))
    val branchingStmt = ast.Inhale(ast.TrueLit()())(pos(5, 3))
    val nextStmt = ast.Exhale(ast.TrueLit()())(pos(9, 3))

    val log = root.openMemberScope(method, null)
    val branchingId = log.openScope(new ExecuteRecord(branchingStmt, null, null))
    val branchPoint = log.insertBranchPoint(2, Some(terms.True), None)

    /* Scope of the branching statement is closed within both branches, i.e. the continuation runs on each branch */
    log.markReachable(branchPoint)
    log.closeScope(branchingId)
    log.switchToNextBranch(branchPoint)
    log.markReachable(branchPoint)
    log.closeScope(branchingId)
    log.endBranchPoint(branchPoint)

    val nextId = log.openScope(new ExecuteRecord(nextStmt, null, null))

    Thread.sleep(3 * reportAfterMillis)

    val messages = reporter.stateMessages
    messages should have size 1
    messages.head.state.render.linesIterator.toSeq shouldBe Seq(
      "method m (3:1)",
      "execute exhale true (9:3)")

    log.closeScope(nextId)
    log.closeMemberScope()
    root.close()
  }
}
