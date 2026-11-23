// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon
import viper.silver.reporter.{InternalWarningMessage, Message, Reporter, WarningsDuringVerification}

import scala.collection.mutable.ArrayBuffer

/** Verifies the test programs in triggers/ and checks that Silicon reports no warning that a trigger might not be
  * usable ("Might not be able to use trigger") or could not be resolved while axiomatising a function ("Could not
  * resolve expression"). SiliconTests, which also verifies these programs, checks their annotated errors, but not
  * warnings.
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

  private def check(fileName: String): Unit = {
    val program = _root_.tests.loadProgram("triggers/", fileName, frontend)
    reporter.clear()
    silicon.verify(program)

    val triggerWarnings = reporter.warnings.filter(w =>
      w.contains("Might not be able to use trigger") || w.contains("Could not resolve expression"))
    assert(triggerWarnings.isEmpty, s"Unexpected trigger warnings: ${triggerWarnings.mkString("\n")}")
  }

  test("Triggers with nested lets are found in the quantifier body") {
    check("lets_in_triggers")
  }

  test("Triggers that are lets are found in the quantifier body") {
    check("top_level_lets_in_triggers")
  }
}
