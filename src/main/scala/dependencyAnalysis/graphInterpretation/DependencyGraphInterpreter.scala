// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graphInterpretation

import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.interfaces.Failure
import viper.silver.ast
import viper.silver.ast.Program
import viper.silver.dependencyAnalysis.{AssumptionType, JoinType}

import java.io.PrintWriter
import java.nio.file.Paths

object DATraversalMode extends Enumeration {
  type DATraversalMode = Value
  val Upwards, Downwards = Value
}

class DependencyGraphInterpreter[T <: DependencyGraphState](name: String, dependencyGraph: ReadOnlyDependencyGraph[T], errors: List[Failure], member: Option[ast.Member]=None) {
  val pruningSupporter: DependencyAnalysisPruningSupporter[T] = new DependencyAnalysisPruningSupporter[T](this)
  val progressSupporter: DependencyAnalysisProgressSupporter[T] = new DependencyAnalysisProgressSupporter[T](this)


  def getGraph: ReadOnlyDependencyGraph[T] = dependencyGraph

  def getName: String = name

  def getMember: Option[ast.Member] = member

  def getNodes: Set[DependencyAnalysisNode] = dependencyGraph.getNodes

  def getAssumptionNodes: Set[GeneralAssumptionNode] = dependencyGraph.getAssumptionNodes

  def getAssertionNodes: Set[GeneralAssertionNode] = dependencyGraph.getAssertionNodes

  def getErrors: List[Failure] = errors

  // TODO ake: join nodes are not needed for the final graph. Maybe we can outsource this to a dedicated intraprocedural graph interpreter class.
  val joinSinkNodes: Set[DependencyAnalysisNode] = getJoinCandidateNodes(getNodes).filter(_.joinInfos.exists(_.joinType.equals(JoinType.Sink)))
  val joinSourceNodes: Set[DependencyAnalysisNode] = getJoinCandidateNodes(getNodes).filter(_.joinInfos.exists(_.joinType.equals(JoinType.Source)))

  private def getJoinCandidateNodes(nodes: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = nodes.filter(node => node.joinInfos.nonEmpty)

  def toUserLevelNodes(nodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = UserLevelDependencyAnalysisNode.from(nodes)

  def getNodesByLine(line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(isVisibleNode).filter(node => node.sourceInfo.getLineNumber.contains(line))

  def getNodesByPosition(file: String, line: Int): Set[DependencyAnalysisNode] =
    getNodes.filter(isVisibleNode).filter(node => node.sourceInfo.getLineNumber.contains(line) && node.sourceInfo.getPositionString.startsWith(file + "."))


  def getNodesByLabel(label: String): Set[DependencyAnalysisNode] = {
    val fullAnnotation = ("""@label\(\s*"?""" + java.util.regex.Pattern.quote(label) + """"?\s*\)""").r
    getNodes.filter(node => fullAnnotation.findFirstIn(node.toString).isDefined)
  }

  def computeDirectDependencies(nodesToAnalyze: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
    val result = dependencyGraph.computeDirectDependencies(nodesToAnalyze, includeInfeasibilityNodes = true, includeUpwardEdges = true, includeDownwardEdges = true)
    result filter isNonInternalAssumptionNode
  }

  private def computeDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependenciesUpwards = dependencyGraph.computeDependencies(nodesToAnalyze, includeInfeasibilityNodes, includeUpwardEdges = true, includeDownwardEdges = false)
    val allDependenciesDownwards = dependencyGraph.computeDependencies(nodesToAnalyze ++ allDependenciesUpwards, includeInfeasibilityNodes, includeUpwardEdges = false, includeDownwardEdges = true)
    allDependenciesUpwards ++ allDependenciesDownwards
  }

  def computeNonInternalDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    computeDependencies(nodesToAnalyze, includeInfeasibilityNodes) filter isNonInternalAssumptionNode
  }

  def computeExplicitDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDeps = computeDependencies(nodesToAnalyze, includeInfeasibilityNodes)
    allDeps filter isExplicitAssumptionNode
  }

  def computeDirectDependents(nodesToAnalyze: Set[DependencyAnalysisNode]): Set[DependencyAnalysisNode] = {
    val result = dependencyGraph.computeDirectDependents(nodesToAnalyze, includeInfeasibilityNodes = true, includeUpwardEdges = true, includeDownwardEdges = true)
    result filter isNonInternalAssertionNode
  }

  private def computeDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDependentsDownwards = dependencyGraph.computeDependents(nodesToAnalyze, includeInfeasibilityNodes, includeUpwardEdges = false, includeDownwardEdges = true)
    val allDependentsUpwards = dependencyGraph.computeDependents(nodesToAnalyze ++ allDependentsDownwards, includeInfeasibilityNodes, includeUpwardEdges = true, includeDownwardEdges = false)
    allDependentsUpwards ++ allDependentsDownwards
  }

  def computeNonInternalDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDeps = computeDependents(nodesToAnalyze, includeInfeasibilityNodes)
    allDeps filter isNonInternalAssertionNode
  }

  def computeExplicitDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean = true): Set[DependencyAnalysisNode] = {
    val allDeps = computeDependents(nodesToAnalyze, includeInfeasibilityNodes)
    allDeps filter isExplicitAssertionNode
  }

  private def isVisibleNode(node: DependencyAnalysisNode): Boolean =
    !node.assumptionType.isInstanceOf[AssumptionType.InternalType]

  def getNonInternalAssumptionNodes: Set[DependencyAnalysisNode] = getNodes filter isNonInternalAssumptionNode

  def isNonInternalAssumptionNode(node: DependencyAnalysisNode): Boolean = {
    node match {
      case _: GeneralAssumptionNode if isVisibleNode(node) => true
      case _ => false
    }
  }

  private def isExplicitAssumptionNode(node: DependencyAnalysisNode): Boolean = node match {
    case node: GeneralAssumptionNode => node.assumptionType.isInstanceOf[AssumptionType.ExplicitAssumptionType]
    case _ => false
  }

  def getNonInternalAssertionNodes: Set[GeneralAssertionNode] =
    getAssertionNodes filter isNonInternalAssertionNode

  private def isNonInternalAssertionNode(node: DependencyAnalysisNode): Boolean = node match {
    case node: GeneralAssertionNode if isVisibleNode(node) => true
    case _ => false
  }

  def getExplicitAssertionNodes: Set[GeneralAssertionNode] =
    getAssertionNodes filter isExplicitAssertionNode

  private def isExplicitAssertionNode(node: DependencyAnalysisNode): Boolean = node.assumptionType.isInstanceOf[AssumptionType.ExplicitAssertionType]

  def getAssertionNodesWithFailures: Set[GeneralAssertionNode] =
    getNonInternalAssertionNodes filter (_.hasFailed)

  def exportGraph(program: ast.Program, exportPath: String): Unit = {
    if (exportPath.isEmpty) return
    val directory = Paths.get(exportPath).toFile
    directory.mkdirs()
    dependencyGraph.exportGraph(exportPath)
    exportProgram(program, exportPath)
  }

  private def exportProgram(program: Program, path: String): Unit = {
    // TODO ake: we should copy the original source file in order to keep the line numbering!
    val writer = new PrintWriter(path + "/program.vpr")
    writer.println(program.toString())
    writer.close()
  }
}
