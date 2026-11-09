// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter

trait AbstractDependencyAnalysisCliTool {
  val interpreter: DependencyGraphInterpreter[Final]

  protected def getSourceInfoString(nodes: Set[DependencyAnalysisNode]): String = {
    UserLevelDependencyAnalysisNode.mkUserLevelString(nodes, "\n\t")
  }

  protected def getQueriedNodesFromInput(inputs: Set[String]): Set[DependencyAnalysisNode] = {
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

  protected def measureTime[T](function: => T): (T, Double) = {
    val startAnalysis = System.nanoTime()
    val res = function
    val endAnalysis = System.nanoTime()
    val durationMs = (endAnalysis - startAnalysis) / 1e6
    (res, durationMs)
  }
}


trait DependencyAnalysisCliToolExtension extends AbstractDependencyAnalysisCliTool {
  val name: String
  val commands: List[DependencyAnalysisCliCommand]

  def getInfoString(separator: String): String = s"$name$separator\t${commands.map(_.description).mkString(s"$separator\t")}"

  def visit(inputs: Seq[String]): Boolean = commands map (_.visit(inputs)) exists identity
}

trait DependencyAnalysisCliCommand {
  val cmdName: String
  val cmd: Seq[String] => Unit
  val description: String

  def accept(inputs: Seq[String]): Boolean = inputs.nonEmpty && inputs.head.equalsIgnoreCase(cmdName)

  def visit(inputs: Seq[String]): Boolean = {
    val accepted = accept(inputs)
    if (accepted) cmd(inputs.tail)
    accepted
  }
}
