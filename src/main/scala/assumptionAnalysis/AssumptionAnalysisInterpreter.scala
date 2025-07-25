package viper.silicon.assumptionAnalysis

import viper.silicon.state.terms.True
import viper.silicon.verifier.Verifier
import viper.silver.ast

import scala.collection.mutable

object AssumptionAnalysisInterpreter {
  def joinGraphsAndGetInterpreter(name: Option[String], assumptionAnalysisInterpreters: Set[AssumptionAnalysisInterpreter]): AssumptionAnalysisInterpreter = {
    val newGraph = new AssumptionAnalysisGraph

    assumptionAnalysisInterpreters foreach (interpreter => newGraph.addNodes(interpreter.getGraph.getNodes))
    assumptionAnalysisInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (s, t) => newGraph.addEdges(s, t)})

    val types = Set(AssumptionType.Implicit, AssumptionType.Explicit)
    val relevantAssumptionNodes = newGraph.nodes filter (node => node.isInstanceOf[GeneralAssumptionNode] && types.contains(node.assumptionType))

    newGraph.nodes filter (node => node.isInstanceOf[GeneralAssertionNode] && node.assumptionType.equals(AssumptionType.Postcondition)) foreach {node => // TODO ake: check if this also works for functions
      val nodeSourceInfoString = node.sourceInfo.getTopLevelSource.toString
      val assumptionNodesForJoin = relevantAssumptionNodes filter (aNode => aNode.sourceInfo.getFineGrainedSource.toString.equals(nodeSourceInfoString))
      newGraph.addEdges(node.id, assumptionNodesForJoin map (_.id))
    }

    new AssumptionAnalysisInterpreter(name.getOrElse("joined"), newGraph)
  }
}

class AssumptionAnalysisInterpreter(name: String, graph: ReadOnlyAssumptionAnalysisGraph, member: Option[ast.Member]=None) {
  private def getGraph: ReadOnlyAssumptionAnalysisGraph = graph
  def getName: String = name
  def getMember: Option[ast.Member] = member
  def getNodes: Set[AssumptionAnalysisNode] = graph.getNodes.toSet

  def getNodesByLine(line: Int): Set[AssumptionAnalysisNode] =
    getNodes.filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line)

  def getNodesByPosition(file: String, line: Int): Set[AssumptionAnalysisNode] =
    getNodes.filter(node => node.sourceInfo.getLineNumber.isDefined && node.sourceInfo.getLineNumber.get == line && node.sourceInfo.getPositionString.startsWith(file + ".vpr"))

  def getDirectDependencies(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] =
    getNonInternalAssumptionNodes.filter(node => graph.getDirectEdges.get(node.id).exists(_.intersect(nodeIdsToAnalyze).nonEmpty))

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] =
    getNonInternalAssumptionNodes.filter(node => graph.existsAnyDependency(Set(node.id), nodeIdsToAnalyze))

  def getAllExplicitDependencies(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] =
    getExplicitAssumptionNodes.filter(node => graph.existsAnyDependency(Set(node.id), nodeIdsToAnalyze))


  def getAllNonInternalDependents(nodeIdsToAnalyze: Set[Int]): Set[AssumptionAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => graph.existsAnyDependency(nodeIdsToAnalyze, Set(node.id)))


  def getNonInternalAssumptionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
      (node.isInstanceOf[GeneralAssumptionNode] && !node.assumptionType.equals(AssumptionType.Internal)) ||
      (node.isInstanceOf[GeneralAssertionNode] && node.assumptionType.equals(AssumptionType.Postcondition))
    )

  def getExplicitAssumptionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
    node.assumptionType.equals(AssumptionType.Explicit) || node.assumptionType.equals(AssumptionType.Postcondition))

  private def getNonInternalAssumptionNodesPerSource: Map[String, Set[AssumptionAnalysisNode]] =
    getNonInternalAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)


  def getNonInternalAssertionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
      node.isInstanceOf[GeneralAssertionNode] && !node.assumptionType.equals(AssumptionType.Internal)
    )

  def getExplicitAssertionNodes: Set[AssumptionAnalysisNode] =
    getNonInternalAssertionNodes.filter(node =>
      node.assumptionType.equals(AssumptionType.Postcondition) || node.assumptionType.equals(AssumptionType.Explicit))


  def exportGraph(): Unit = {
    if(Verifier.config.assumptionAnalysisExportPath.isEmpty) return
    graph.exportGraph(Verifier.config.assumptionAnalysisExportPath() + "/" + name)
  }

  def computeProofCoverage(): (Double, Seq[String]) = {
    val explicitAssertionNodes = getExplicitAssertionNodes
    computeProofCoverage(explicitAssertionNodes)
  }

  def computeProofCoverage(assertionNodes: Set[AssumptionAnalysisNode]): (Double, Seq[String]) = {
    val assertionNodeIds = assertionNodes map (_.id)
    val nodesPerSourceInfo = getNonInternalAssumptionNodesPerSource
    if(nodesPerSourceInfo.isEmpty) return (Double.NaN, Seq())

    val uncoveredSources = (nodesPerSourceInfo filter { case (_, nodes) =>
      val nodeIds = nodes map (_.id)
      // it is not an explicit assertion itself and has no dependency to an explicit assertion
      nodeIds.intersect(assertionNodeIds).isEmpty &&
        !graph.existsAnyDependency(nodeIds, assertionNodeIds)
    }).keys.toSeq
    val proofCoverage = 1.0 - (uncoveredSources.size.toDouble / nodesPerSourceInfo.size.toDouble)
    (proofCoverage, uncoveredSources)
  }
}
