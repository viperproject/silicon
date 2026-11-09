// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter

/**
 * A parsed command line.
 *
 * @param args the arguments following the command name
 * @param exportTarget the text following '>', if any
 */
case class DependencyAnalysisCliInput(args: Seq[String], exportTarget: Option[String])

/**
 * The output of a command, which is written out by a [[DependencyAnalysisCliConsole]].
 */
case class DependencyAnalysisCliResult(lines: String*)

object DependencyAnalysisCliResult {
  val empty: DependencyAnalysisCliResult = DependencyAnalysisCliResult()
}

/**
 * The connection of the CLI tool to its user. Commands normally just return a [[DependencyAnalysisCliResult]].
 * Only commands that prompt for input or report progress while running need access to the console directly.
 */
trait DependencyAnalysisCliConsole {
  def readLine(): String
  def printLine(line: String): Unit

  final def print(result: DependencyAnalysisCliResult): Unit = result.lines foreach printLine
}

object StdDependencyAnalysisCliConsole extends DependencyAnalysisCliConsole {
  override def readLine(): String = scala.io.StdIn.readLine()
  override def printLine(line: String): Unit = println(line)
}

trait DependencyAnalysisCliCommand {
  val cmdName: String
  val aliases: List[String] = List.empty
  val listedInHelp: Boolean = true
  val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult
  val description: String

  /**
   * @param inputs the command line split into words, starting with the command name
   */
  def accept(inputs: Seq[String]): Boolean = inputs.nonEmpty && (cmdName :: aliases).exists(inputs.head.equalsIgnoreCase)
}

/**
 * A named group of commands that is listed separately in the command overview.
 */
trait DependencyAnalysisCliToolExtension {
  val name: String
  val commands: List[DependencyAnalysisCliCommand]

  def getInfoString(separator: String): String = s"$name$separator\t${commands.map(_.description).mkString(s"$separator\t")}"
}

object DependencyAnalysisCliSupport {
  def getSourceInfoString(nodes: Set[DependencyAnalysisNode]): String = {
    UserLevelDependencyAnalysisNode.mkUserLevelString(nodes, "\n\t")
  }

  def getQueriedNodesFromInput(interpreter: DependencyGraphInterpreter[Final], inputs: Set[String]): Set[DependencyAnalysisNode] = {
    inputs flatMap (input => {
      val parts = input.split("@")
      if (parts.size == 2)
        parts(1).toIntOption.map(interpreter.getNodesByPosition(parts(0), _)).getOrElse(Set.empty)
      else if (parts.size == 1) {
        parts(0).toIntOption map interpreter.getNodesByLine getOrElse Set.empty
      } else {
        Set.empty
      }
    })
  }

  def measureTime[T](function: => T): (T, Double) = {
    val startAnalysis = System.nanoTime()
    val res = function
    val endAnalysis = System.nanoTime()
    val durationMs = (endAnalysis - startAnalysis) / 1e6
    (res, durationMs)
  }
}
