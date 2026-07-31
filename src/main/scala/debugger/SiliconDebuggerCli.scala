// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

/**
  * The command-line frontend of the debugger: a REPL on top of [[SiliconDebugSession]].
  *
  * Input and output are injectable so that the REPL can be tested without a terminal.
  */
class SiliconDebuggerCli(session: SiliconDebugSession,
                         in: () => String = () => scala.io.StdIn.readLine(),
                         out: String => Unit = println) {

  def run(): Unit = {
    if (!session.config.enableDebugging()) {
      out("Debugging mode is disabled")
      return
    }
    val failures = session.failures
    if (failures.isEmpty) {
      out("No failures found. Debugging mode terminated.")
      return
    }

    while (true) {
      failures.foreach(f => out(s"[${f.index}]: ${f.message} (${f.posString})\n"))
      if (failures.size == 1) {
        if (open(0)) debugProofObligation()
        return
      } else {
        out(s"Which verification result do you want to debug next [0 - ${failures.size - 1}] (or q to quit):")
        val userInput = readLineOr("q")
        if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
          return
        }
        val idx = userInput.toIntOption.getOrElse(-1)
        if (open(idx)) debugProofObligation()
      }
    }
  }

  private def open(idx: Int): Boolean = {
    val res = session.openObligation(idx)
    report(res)
    res.ok
  }

  private def debugProofObligation(): Unit = {
    while (true) {
      out(s"\nEnter 'q' to quit, 'z' to zoom in on (i.e., show all children of) an assumption, " +
        s"'r' to reset the proof obligation, 'ra' to remove assumptions, 'af' to add free assumptions, " +
        s"'ap' prove additional assumptions, 'p' to execute proof, 'x' to show a counterexample, " +
        s"'c' to change print configuration, 's' to change the SMT solver, 't' to change the timeout")
      try {
        val command = readLine()
        if (command == null) return
        command.toLowerCase match {
          case "q" | "quit" => return
          case "z" | "zoom" => zoom()
          case "r" | "reset" => report(session.reset())
          case "ra" | "remove" | "remove assumption" => removeAssumptions()
          case "af" | "assume" | "add free assumption" => addAssumption(free = true)
          case "ap" | "assert" | "add and prove assumption" => addAssumption(free = false)
          case "p" | "prove" => report(session.prove(), printObligation = false)
          case "x" | "ce" | "counterexample" => showCounterexample()
          case "c" | "config" => changePrintConfiguration()
          case "s" | "solver" | "choose different SMT solver" => changeSolver()
          case "t" | "timeout" => setTimeout()
          case _ => out("Invalid input!")
        }
      } catch {
        case e: Throwable => out(s"Unexpected error: ${e.getMessage}. \nTry again")
      }
    }
  }

  /** Shows the model of the last failed proof attempt, running the prover first if necessary. */
  private def showCounterexample(): Unit = {
    if (session.currentObligation.flatMap(_.counterexample).isEmpty) {
      out("No counterexample is available yet; proving the obligation to obtain one...")
      report(session.prove(), printObligation = false)
    }
    session.currentObligation.flatMap(_.counterexample) match {
      case Some(ce) => out(s"\nCounterexample:\n${DebugRenderer.renderCounterexample(ce)}")
      case None => out("No counterexample is available.")
    }
  }

  private def zoom(): Unit = {
    out("Enter the assumption you want to zoom in on:")
    readLineOr("").trim.toIntOption match {
      case Some(id) =>
        session.expand(id) match {
          case Left(err) => out(err)
          case Right(nodes) => if (nodes.nonEmpty) out(s"${DebugRenderer.renderNodes(nodes, 0)}\n\n")
        }
      case None => out("Invalid input")
    }
  }

  private def removeAssumptions(): Unit = {
    out("Enter the assumptions you want to remove:")
    val indices = readLineOr("").split(",").flatMap(s => s.trim.toIntOption).toSeq
    report(session.removeAssumptions(indices))
  }

  private def addAssumption(free: Boolean): Unit = {
    out("Enter the assumption you want to add or s(skip):")
    val userInput = readLineOr("s")
    if (userInput.isEmpty || userInput.equalsIgnoreCase("s") || userInput.equalsIgnoreCase("skip")) {
      return
    }
    report(session.addAssumption(userInput, free))
  }

  private def setTimeout(): Unit = {
    out("Enter new timeout in ms, 0 for no timeout:")
    val timeoutInput = readLineOr("")
    try {
      val timeoutInt = Integer.parseUnsignedInt(timeoutInput)
      report(session.setTimeout(if (timeoutInt == 0) None else Some(timeoutInt)), printObligation = false)
    } catch {
      case _: NumberFormatException => out("Invalid timeout value.")
    }
  }

  private def changeSolver(): Unit = {
    out(s"Enter SMT solver to use. Options are ${SiliconDebugSession.proverNames.mkString(", ")}:")
    val solverNameInput = readLineOr("")
    if (!SiliconDebugSession.proverNames.contains(solverNameInput)) {
      out("Invalid prover name.")
    } else {
      out("Enter any additional command line options for the prover, separated by spaces:")
      val solverArgsInput = readLineOr("")
      report(session.setProver(solverNameInput, Some(solverArgsInput).filter(_.nonEmpty)), printObligation = false)
    }
  }

  private def changePrintConfiguration(): Unit = {
    val current = session.currentObligation.map(_.printConfig).getOrElse(new DebugExpPrintConfiguration().toModel)
    out(s"Current configuration:\n${renderPrintConfig(current)}")

    def readBool(name: String, old: Boolean): Boolean = {
      out(s"Enter the new value for $name:")
      readLineOr("").toLowerCase match {
        case "true" | "1" | "t" => true
        case "false" | "0" | "f" => false
        case _ => old
      }
    }

    val printInternal = readBool("isPrintInternalEnabled", current.printInternal)

    out("Enter the new value for nChildrenToShow:")
    val nChildren = readLineOr("").toIntOption.getOrElse(current.nChildrenToShow)

    out("Enter the new value for printHierarchyLevel:")
    val level = readLineOr("") match {
      case "full" => 100
      case "top" => 0
      case other => other.toIntOption.getOrElse(current.hierarchyLevel)
    }

    val printAxioms = readBool("isPrintAxiomsEnabled", current.printAxioms)
    val printTerms = readBool("printInternalTermRepresentation", current.printInternalTermRepresentation)
    val printOldHeaps = readBool("printOldHeaps", current.printOldHeaps)

    report(session.setPrintConfig(PrintConfigModel(printInternal, nChildren, level, printAxioms, printTerms, printOldHeaps)))
  }

  private def renderPrintConfig(c: PrintConfigModel): String =
    s"  isPrintInternalEnabled = ${c.printInternal}\n" +
      s"  nChildrenToShow        = ${c.nChildrenToShow}\n" +
      s"  printHierarchyLevel    = ${c.hierarchyLevel}\n" +
      s"  isPrintAxiomsEnabled   = ${c.printAxioms}\n" +
      s"  printInternalTermReps  = ${c.printInternalTermRepresentation}\n" +
      s"  printOldHeaps          = ${c.printOldHeaps}\n"

  /** Reads a line, falling back to `default` when the input stream has reached its end. */
  private def readLineOr(default: String): String = Option(in()).getOrElse(default)

  private def readLine(): String = in()

  private def report(res: DebugCommandResult, printObligation: Boolean = true): Unit = {
    res.messages.foreach(m => out(m.text))
    if (printObligation) {
      res.obligation.foreach(o => out(s"Current obligation:\n${DebugRenderer.renderObligation(o)}"))
    }
  }
}
