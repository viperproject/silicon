// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, AssumptionType}

class DebugDependencyAnalysisCliExtension(override val interpreter: DependencyGraphInterpreter[Final]) extends DependencyAnalysisCliToolExtension{
  override val name: String = "Debug Features"
  override val commands: List[DependencyAnalysisCliCommand] = List(
                                                                new AssumptionTypesCommand,
                                                                new AssertionTypesCommand,
                                                                new LowLevelNodesCommand,
                                                                new WeirdNodesCommand
                                                              )

  class AssumptionTypesCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "assumptionTypes"
    override val cmd: Seq[String] => Unit = { inputs =>
      if (inputs.isEmpty)
        println(getAssumptionTypesPerNode().mkString("\n"))
      else
        inputs.flatMap(_.toIntOption).foreach(i => println(s"$i: ${getAssumptionTypesByLine(i)}"))
    }
    override val description: String = s"'$cmdName [line numbers]' to print the assumption types of all nodes or just the provided lines"

    private def getAssumptionTypesByLine(line: Int): Set[AssumptionType] = {
      interpreter.getNodesByLine(line).filter(_.isInstanceOf[GeneralAssumptionNode]).map(_.assumptionType)
    }

    private def getAssumptionTypesPerNode(): Map[AnalysisSourceInfo, Set[AssumptionType]] =
      getAssumptionTypesPerNode(interpreter.getAssumptionNodes)

    private def getAssumptionTypesPerNode(nodes: Set[DependencyAnalysisNode]): Map[AnalysisSourceInfo, Set[AssumptionType]] =
      nodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.assumptionType)).toMap
  }

  class AssertionTypesCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "assertionTypes"
    override val cmd: Seq[String] => Unit = { inputs =>
      if (inputs.isEmpty)
        println(getAssertionTypesPerNode().mkString("\n"))
      else
        inputs.flatMap(_.toIntOption).foreach(i => println(s"$i: ${getAssertionTypesByLine(i)}"))
    }
    override val description: String = s"'$cmdName [line numbers]' to print the assertion types of all nodes or just the provided lines"

    private def getAssertionTypesByLine(line: Int): Set[AssumptionType] = {
      interpreter.getNodesByLine(line).filter(_.isInstanceOf[GeneralAssertionNode]).map(_.assumptionType)
    }

    private def getAssertionTypesPerNode(): Map[AnalysisSourceInfo, Set[AssumptionType]] =
      getAssertionTypesPerNode(interpreter.getAssertionNodes)

    private def getAssertionTypesPerNode(nodes: Set[DependencyAnalysisNode]): Map[AnalysisSourceInfo, Set[AssumptionType]] =
      nodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.assumptionType)).toMap
  }

  class LowLevelNodesCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "lowLevelNodes"
    override val cmd: Seq[String] => Unit = inputs =>
      inputs.flatMap(_.toIntOption).foreach(i => println(s"$i:\n\t${getLowLevelNodesByLine(i).mkString("\n\t")}"))
    override val description: String = s"'$cmdName [line numbers]' to print all low-level nodes of the provided lines"

    override def accept(inputs: Seq[String]): Boolean = super.accept(inputs) && inputs.tail.nonEmpty

    private def getLowLevelNodesByLine(line: Int): List[DependencyAnalysisNode] = {
      interpreter.getNodesByLine(line).toList.sortBy(_.id)
    }
  }

  class WeirdNodesCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "weirdNodes"
    override val cmd: Seq[String] => Unit = _ => printWeirdNodes()
    override val description: String = s"'$cmdName' to print weird nodes"
    private val weirdNodePattern = """\b(function|func|method|domain|if|else|while|for|match|interface|struct|package|import|type)\b""".r

    private def printWeirdNodes(): Unit = {
      interpreter.getNodes.filter(n => !AssumptionType.internalTypes.contains(n.assumptionType)).groupBy(_.sourceInfo)
        .filter{case (sourceInfo, _) => weirdNodePattern.findFirstIn(sourceInfo.toString).isDefined}
				.foreach{case (sourceInfo, nodes) => println(s"\n-- ${sourceInfo.toString}\n\t${nodes.map(n => s"${n.getNodeString} | ${n.assumptionType}").mkString("\n\t")}\n--")}

    }
  }
}
