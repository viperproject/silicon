// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.DependencyAnalysisOptions
import viper.silicon.dependencyAnalysis.graphInterpretation.FinalGraphInterpreter
import viper.silicon.interfaces.Failure
import viper.silver.ast

import scala.annotation.tailrec

object DependencyAnalysisCliTool {
  /**
   * @return a CLI tool offering all available commands for the given analysis result
   */
  def apply(queries: FinalGraphInterpreter, program: ast.Program, verificationErrors: List[Failure],
            options: DependencyAnalysisOptions, console: DependencyAnalysisCliConsole = StdDependencyAnalysisCliConsole): DependencyAnalysisCliTool = {
    new DependencyAnalysisCliTool(
      new CoreDependencyAnalysisCliCommands(queries, program, verificationErrors).commands,
      List(
        new DebugDependencyAnalysisCliExtension(queries, options),
        new TestDependencyAnalysisCliExtension(queries, console),
        new BenchmarkDependencyAnalysisCliExtension(queries, program, console)
      ),
      verificationErrors.nonEmpty || queries.getAssertionNodesWithFailures.nonEmpty,
      console
    )
  }
}

/**
 * Parses command lines, runs the matching command, and writes out its result.
 *
 * @param coreCommands commands listed individually in the command overview
 * @param extensions groups of further commands
 * @param programHasFailures whether the analyzed program failed to verify; only evaluated in interactive mode
 */
class DependencyAnalysisCliTool(coreCommands: List[DependencyAnalysisCliCommand],
                                extensions: List[DependencyAnalysisCliToolExtension],
                                programHasFailures: => Boolean,
                                console: DependencyAnalysisCliConsole) {

  private val helpCommand: DependencyAnalysisCliCommand = new DependencyAnalysisCliCommand {
    override val cmdName: String = "help"
    override val aliases: List[String] = List("h")
    override val description: String = "`help` to print this command overview"
    override val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult = _ => DependencyAnalysisCliResult(infoString)
  }

  private val listedCommands: List[DependencyAnalysisCliCommand] = helpCommand :: coreCommands
  private val allCommands: List[DependencyAnalysisCliCommand] = listedCommands ++ extensions.flatMap(_.commands)

  /**
   * Runs the given commands, which are separated by semicolons, in order.
   */
  def runCommands(commands: String): Unit = {
    if (commands.nonEmpty) {
      commands.split(";").map(_.trim) foreach { command =>
        console.printLine(s"\n--------\nProcessing command \"$command\"...")
        run(command)
      }
    }
  }

  private def run(commandStr: String): Unit = {
    commandStr.toLowerCase() match {
      case "interactive" => handleInteractiveMode()
      case _ => handleCommand(commandStr)
    }
  }

  private def infoString: String = "Enter " +
    listedCommands.filter(_.listedInHelp).map("\n\t" + _.description).mkString +
    (if (extensions.nonEmpty) "\n\t" else "") +
    extensions.map(_.getInfoString("\n\t")).mkString("\n\t") +
    "\n\t'q' to quit"

  private def handleInteractiveMode(): Unit = {
    console.printLine("Dependency Analysis Tool started.")
    console.printLine(infoString)
    if (programHasFailures)
      console.printLine("Program did not verify!")

    runInteractiveMode()
  }

  @tailrec
  private def runInteractiveMode(): Unit = {
    try {
      val userInput = console.readLine()
      if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
        return
      } else if (userInput.nonEmpty) {
        handleCommand(userInput)
      } else {
        console.printLine(infoString)
      }
    } catch {
      case e: Exception => console.printLine("ERROR:\n\t" + e.getMessage)
      case e: AssertionError => console.printLine("ERROR:\n\t" + e.getMessage)
    }
    runInteractiveMode()
  }

  private def handleCommand(commandLine: String): Unit = {
    val exportTarget = commandLine.split(">").tail.headOption.map(_.trim)
    val cmdParts = commandLine.takeWhile(_ != '>').split(" ").toSeq
    if (cmdParts.nonEmpty) {
      allCommands.find(_.accept(cmdParts)) match {
        case Some(command) => console.print(command.cmd(DependencyAnalysisCliInput(cmdParts.tail, exportTarget)))
        case None => console.printLine(s"Unknown command $commandLine.\n$infoString")
      }
      console.printLine("Done.")
    }
  }
}
