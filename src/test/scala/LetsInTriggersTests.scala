// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon
import viper.silver.ast.{Forall, FuncApp, HasLineColumn, Let, Program}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.reporter.{InternalWarningMessage, Message, Reporter, WarningsDuringVerification}
import viper.silver.verifier.{AbstractVerificationError, Failure, Success}

import java.nio.file.{Files, Paths}
import scala.collection.mutable.ArrayBuffer
import scala.jdk.CollectionConverters._

/** Checks that triggers containing lets are found among the terms recorded while evaluating
  * the quantifier body, modulo their lets, instead of being evaluated on their own (which
  * fails for the test programs and makes Silicon drop the trigger with a warning).
  */
class LetsInTriggersTests extends AnyFunSuite with BeforeAndAfterAll {
  private class CollectingReporter extends Reporter {
    val name = "collecting_reporter"
    private val messages = ArrayBuffer[Message]()

    def report(msg: Message): Unit = synchronized { messages += msg }
    def clear(): Unit = synchronized { messages.clear() }
    def warnings: Seq[String] = synchronized {
      messages.toSeq.collect {
        case WarningsDuringVerification(ws) => ws.map(_.readableMessage)
        case InternalWarningMessage(text) => Seq(text)
      }.flatten
    }
  }

  private val reporter = new CollectingReporter

  private val silicon: Silicon = {
    val silicon = new Silicon(reporter, Seq("startedBy" -> "viper.silicon.tests.LetsInTriggersTests"))
    silicon.parseCommandLine(Seq("--ignoreFile", Silicon.dummyInputFilename))
    silicon
  }

  private val frontend = new _root_.tests.DummyFrontend

  override def beforeAll(): Unit = {
    silicon.start()
    frontend.init(silicon)
  }

  override def afterAll(): Unit = {
    silicon.stop()
  }

  /** Replaces each trigger expression `unwrap(e)` or `unwrapInt(e)` by `e`. This allows writing triggers whose
    * top-level expression is a let, which Silver rejects when translating a parsed program,
    * but which Silicon receives from frontends that construct the AST directly.
    */
  private def unwrapTriggers(program: Program): Program =
    program.transform({
      case q: Forall =>
        val triggers = q.triggers.map(t => t.copy(exps = t.exps.map {
          case FuncApp("unwrap" | "unwrapInt", Seq(e)) => e
          case e => e
        })(t.pos, t.info, t.errT))
        q.copy(triggers = triggers)(q.pos, q.info, q.errT)
    }, Traverse.TopDown)

  private def load(filePrefix: String, fileName: String): (Program, Seq[Int]) = {
    val program = unwrapTriggers(_root_.tests.loadProgram(filePrefix, fileName, frontend))
    val lines = Files.readAllLines(Paths.get(getClass.getClassLoader.getResource(s"$filePrefix$fileName.vpr").toURI)).asScala
    val expectedFailureLines =
      lines.zipWithIndex.collect { case (line, idx) if line.trim.startsWith("//:: ExpectedOutput") => idx + 2 }.toSeq
    (program, expectedFailureLines)
  }

  private def check(filePrefix: String, fileName: String, expectTopLevelLets: Boolean): Unit = {
    val (program, expectedFailureLines) = load(filePrefix, fileName)

    val triggerExps = program.deepCollect { case q: Forall => q.triggers.flatMap(_.exps) }.flatten
    assert(triggerExps.exists(_.exists(_.isInstanceOf[Let])), "Test program has no trigger containing a let")
    assert(triggerExps.exists(_.isInstanceOf[Let]) == expectTopLevelLets)

    reporter.clear()
    val result = silicon.verify(program)

    val triggerWarnings = reporter.warnings.filter(w =>
      w.contains("Might not be able to use trigger") || w.contains("Could not resolve expression"))
    assert(triggerWarnings.isEmpty, s"Unexpected trigger warnings: ${triggerWarnings.mkString("\n")}")

    val failureLines = result match {
      case Success => Seq()
      case Failure(errors) => errors.map {
        case e: AbstractVerificationError if e.fullId == "assert.failed:assertion.false" =>
          e.pos.asInstanceOf[HasLineColumn].line
        case e => fail(s"Unexpected error: ${e.readableMessage}")
      }
    }
    assert(failureLines.sorted == expectedFailureLines.sorted)
  }

  test("Triggers with nested lets are found in the quantifier body") {
    check("triggers/", "lets_in_triggers", expectTopLevelLets = false)
  }

  test("Triggers that are lets are found in the quantifier body") {
    check("letsInTriggersTests/", "top_level_lets_in_triggers", expectTopLevelLets = true)
  }
}
