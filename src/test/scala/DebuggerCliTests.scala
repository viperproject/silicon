// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.Silicon
import viper.silicon.debugger.SiliconDebuggerCli

class DebuggerCliTests extends AnyFunSuite {

  /**
    * Runs the debugger's REPL on the only failure of a program. Each input is computed from what the REPL has printed
    * so far, because the ids of assumptions are not known in advance.
    *
    * @return everything the REPL printed.
    */
  private def runCli(fileName: String)(inputs: (String => String)*): String = {
    val backend = new Silicon(List("startedBy" -> s"Unit test ${this.getClass.getSimpleName}"))
    backend.parseCommandLine(List("--enableDebugging", "--ignoreFile", "dummy.sil"))
    backend.start()
    try {
      val frontend = new tests.DummyFrontend
      frontend.init(backend)
      val program = tests.loadProgram("debuggerCli/", fileName, frontend)
      backend.verify(program)

      val output = new StringBuilder
      val remaining = inputs.iterator
      val session = backend.debugSession.getOrElse(fail("no debug session was started"))
      new SiliconDebuggerCli(session,
        () => if (remaining.hasNext) remaining.next()(output.toString) else "q",
        line => output.append(line).append("\n")).run()
      assert(!remaining.hasNext, s"the REPL stopped before reading all inputs:\n$output")
      output.toString
    } finally {
      backend.stop()
    }
  }

  private def line(text: String): String => String = _ => text

  /** The id of the last assumption printed whose text starts with `start`. */
  private def idOf(output: String, start: String): String =
    raw"\[(\d+)\] ".r.findAllMatchIn(output).filter(m => output.startsWith(start, m.end)).toSeq.lastOption
      .map(_.group(1)).getOrElse(fail(s"no assumption starting with $start in:\n$output"))

  test("unfolds and folds a predicate, with the argument on the same line or when asked for it") {
    val output = runCli("fold")(line("u cell(x)"), line("f"), line("cell(x)"), line(":unfold cell(x)"))
    assert(output.contains("Unfolded cell(x"), output)
    assert(output.contains("Enter the predicate instance you want to fold"), output)
    assert(output.contains("Folded cell(x"), output)
    assert(output.contains("(added by: unfold cell(x"), output)
    assert(output.contains("(removed by: unfold cell(x"), output)
    assert(!output.contains("Invalid input"), output)
  }

  test("reports a predicate instance that cannot be unfolded") {
    val output = runCli("fold")(line("u cell(null)"))
    assert(output.contains("Unfolding cell(null) failed"), output)
    assert(!output.contains("Unfolded"), output)
  }

  test("switches between the cases of an unfold, as the debugger's message suggests") {
    val output = runCli("cases")(line("u cond(x, b)"), line(":case 2"), line("cs"), line("1"), line("cs 3"), line("cs two"))
    assert(output.contains("This produced 2 cases"), output)
    assert(output.contains("Showing case 2:") && output.contains("Showing case 1:"), output)
    assert(output.contains("There are only 2 cases."), output)
    assert(!output.contains("Unexpected error"), output)
    assert(output.contains("Invalid input"), output)
  }

  test("instantiates a forall assumption, with the values on the same line or when asked for them") {
    val output = runCli("forall")(
      line("p"),
      o => s"i ${idOf(o, "(forall i@1")} 3",
      line("p"),
      line("r"),
      line("i"),
      o => idOf(o, "(forall i@1"),
      line("3"))
    assert(output.contains("Assumptions added by instantiate ["), output)
    assert(output.contains("FAIL: `g(3) > 0` might not hold"), "g(3) > 0 needs the instance")
    assert(output.contains("PASS: `g(3) > 0` holds"), "g(3) > 0 follows from the instance")
    assert(output.contains("Enter the values to instantiate it with"), output)
    assert(!output.contains("Invalid input"), output)
  }

  test("obtains a witness of an exists assumption and instantiates a forall with it") {
    val output = runCli("exists")(
      o => s"w ${idOf(o, "(exists i@1")}",
      o => s":instantiate ${idOf(o, "(forall i@2")} i_witness@1",
      line("p"))
    assert(output.contains("Assumptions added by witness of ["), output)
    assert(output.contains("i_witness@1"), output)
    assert(output.contains("PASS: "), output)
    assert(!output.contains("Invalid input"), output)
  }

  test("refuses to instantiate an exists or to obtain a witness of a forall") {
    val output = runCli("exists")(
      o => s"i ${idOf(o, "(exists i@1")} 3",
      o => s"w ${idOf(o, "(forall i@2")}",
      line("w nothing"))
    assert(output.contains("use :witness"), output)
    assert(output.contains("is not an exists"), output)
    assert(output.contains("Invalid input"), output)
  }
}
