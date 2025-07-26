package viper.silicon.assumptionAnalysis

import viper.silicon.verifier.Verifier
import viper.silver.ast

import java.io.File

object AssumptionAnalysisInterpreter {
  private val postconditionTypes = Set(AssumptionType.ExplicitPostcondition, AssumptionType.ImplicitPostcondition)

  def joinGraphsAndGetInterpreter(name: Option[String], assumptionAnalysisInterpreters: Set[AssumptionAnalysisInterpreter]): AssumptionAnalysisInterpreter = {
    val newGraph = new AssumptionAnalysisGraph

    assumptionAnalysisInterpreters foreach (interpreter => newGraph.addNodes(interpreter.getGraph.getNodes))
    assumptionAnalysisInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (s, t) => newGraph.addEdges(s, t)})

    // add edges between identical axioms since they were added to each interpreter // TODO ake: merge instead?
    newGraph.getNodes.filter(_.isInstanceOf[AxiomAssumptionNode]).groupBy(n => (n.sourceInfo.toString, n.assumptionType)).foreach{case (_, nodes) =>
      newGraph.addEdges(nodes.map(_.id), nodes.map(_.id))
    }

    val types = Set(AssumptionType.Implicit, AssumptionType.Explicit)
    val relevantAssumptionNodes = newGraph.nodes filter (node => node.isInstanceOf[GeneralAssumptionNode] && types.contains(node.assumptionType))

    newGraph.nodes filter (node => postconditionTypes.contains(node.assumptionType)) foreach { node =>
      val nodeSourceInfoString = node.sourceInfo.getTopLevelSource.toString
      val assumptionNodesForJoin = relevantAssumptionNodes filter (aNode => aNode.sourceInfo.getFineGrainedSource.toString.equals(nodeSourceInfoString))
      newGraph.addEdges(node.id, assumptionNodesForJoin map (_.id))
    }

    new AssumptionAnalysisInterpreter(name.getOrElse("joined"), newGraph)
  }
}

class AssumptionAnalysisInterpreter(name: String, graph: ReadOnlyAssumptionAnalysisGraph, member: Option[ast.Member]=None) {
  protected val explicitAssumptionTypes = Set(AssumptionType.Explicit, AssumptionType.ExplicitPostcondition)
  protected val postconditionTypes = Set(AssumptionType.ExplicitPostcondition, AssumptionType.ImplicitPostcondition)
  protected val explicitAssertionTypes = Set(AssumptionType.Explicit) ++ postconditionTypes

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

  def getAllNonInternalDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] =
    getNonInternalAssumptionNodes.filter(node => graph.existsAnyDependency(Set(node.id), nodeIdsToAnalyze, includeInfeasibilityNodes))

  def getAllExplicitDependencies(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] =
    getExplicitAssumptionNodes.filter(node => graph.existsAnyDependency(Set(node.id), nodeIdsToAnalyze, includeInfeasibilityNodes))


  def getAllNonInternalDependents(nodeIdsToAnalyze: Set[Int], includeInfeasibilityNodes: Boolean = true): Set[AssumptionAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => graph.existsAnyDependency(nodeIdsToAnalyze, Set(node.id), includeInfeasibilityNodes))


  def getNonInternalAssumptionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
      (node.isInstanceOf[GeneralAssumptionNode] && !node.assumptionType.equals(AssumptionType.Internal)) ||
       postconditionTypes.contains(node.assumptionType)
    )

  def getExplicitAssumptionNodes: Set[AssumptionAnalysisNode] = getNonInternalAssumptionNodes filter (node =>
    explicitAssumptionTypes.contains(node.assumptionType)
    )

  private def getNonInternalAssumptionNodesPerSource: Map[String, Set[AssumptionAnalysisNode]] =
    getNonInternalAssumptionNodes.groupBy(_.sourceInfo.getTopLevelSource.toString)


  def getNonInternalAssertionNodes: Set[AssumptionAnalysisNode] = getNodes filter (node =>
    (node.isInstanceOf[GeneralAssertionNode] && !node.assumptionType.equals(AssumptionType.Internal)) ||
      postconditionTypes.contains(node.assumptionType)
    )

  def getExplicitAssertionNodes: Set[AssumptionAnalysisNode] =
    getNonInternalAssertionNodes.filter(node => explicitAssertionTypes.contains(node.assumptionType))


  def exportGraph(): Unit = {
    if(Verifier.config.assumptionAnalysisExportPath.isEmpty) return
    val directory = new File(Verifier.config.assumptionAnalysisExportPath())
    directory.mkdir()
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
        !graph.existsAnyDependency(nodeIds, assertionNodeIds, includeInfeasibilityNodes=true)
    }).keys.toSeq
    val proofCoverage = 1.0 - (uncoveredSources.size.toDouble / nodesPerSourceInfo.size.toDouble)
    (proofCoverage, uncoveredSources)
  }
}
