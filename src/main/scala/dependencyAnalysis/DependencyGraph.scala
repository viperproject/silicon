// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silver.dependencyAnalysis.{AnalysisSourceInfo, AssumptionType}

import java.io.PrintWriter
import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object DependencyGraphHelper {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  /**
   * Helper function used to ensure uniqueness of all dependency node ids.
   */
  def nextId(): Int = {
    idCounter.getAndIncrement()
  }
}

trait DependencyGraphState
class Init extends DependencyGraphState
class IntraProcedural extends DependencyGraphState
class Final extends DependencyGraphState

trait ReadOnlyDependencyGraph[T <: DependencyGraphState] {
  def getNodes: Set[DependencyAnalysisNode]
  def getAssumptionNodes: Set[GeneralAssumptionNode]
  def getAssertionNodes: Set[GeneralAssertionNode]

  def getAssumptionNodeById(id: Int): Option[DependencyAnalysisNode]
  def getAssertionNodeById(id: Int): Option[DependencyAnalysisNode]
  def getNodeById(id: Int): Option[DependencyAnalysisNode]

  /**
   * @return a map from node to the set of direct dependencies in the intraprocedural graph
   */
  def getIntraMethodEdges: Map[Int, Set[Int]]

  /**
   * @return all interprocedural downward edges in the graph as a map from node to all its direct downward dependencies.
   *         A downward edge connects a node representing the proof of a property to a node representing the assumption of
   *         said property in another verification component.
   *         For example, a downward edge may connect a postcondition with a corresponding method call.
   */
  def getEdgesConnectingMethodsDownwards: Map[Int, Set[Int]]

  /**
   * @return all interprocedural upwards edges in the graph as a map from node to all its direct upwards dependencies.
   *         An upwards edge connects a node justifying an assumption (by proving it) to a node representing the specification
   *         element depending on it in another verification component.
   *         For example, an upwards edge may connect a method call with a corresponding precondition.
   */
  def getEdgesConnectingMethodsUpwards: Map[Int, Set[Int]] // e.g. edges connecting PREconditions with method/function calls

  /**
   * @return a map from node to the set of direct dependencies, where all types of edges are included
   */
  def getAllEdges: Map[Int, Set[Int]]

  /**
   * @param includeUpwardEdges: if set to true, interprocedural upward edges are included in the result
   * @param includeDownwardEdges: if set to true, interprocedural downward edges are included in the result
   * @return a map from node to the set of direct dependencies
   */
  def getAllEdges(includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Map[Int, Set[Int]]

  /**
   * @param nodesToAnalyze the set of dependency nodes for which all dependencies should be computed
   * @param includeInfeasibilityNodes if set to true, dependencies found via infeasibility nodes are included in the result
   * @param includeUpwardEdges if set to true, interprocedural upward edges are taken into account
   * @param includeDownwardEdges if set to true, interprocedural downward edges are taken into account
   * @return the set of dependencies of the provided sources
   */
  def computeDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode]

  /**
   * @param nodesToAnalyze the set of dependency nodes for which all dependents should be computed
   * @param includeInfeasibilityNodes if set to true, dependents found via infeasibility nodes are included in the result
   * @param includeUpwardEdges if set to true, interprocedural upward edges are taken into account
   * @param includeDownwardEdges if set to true, interprocedural downward edges are taken into account
   * @return the set of dependents of the provided sources
   */
  def computeDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode]

  /**
   * @param nodesToAnalyze the set of dependency nodes for which the direct dependencies should be computed
   * @param includeInfeasibilityNodes if set to true, dependencies found via infeasibility nodes are included in the result
   * @param includeUpwardEdges if set to true, interprocedural upward edges are taken into account
   * @param includeDownwardEdges if set to true, interprocedural downward edges are taken into account
   * @return the set of direct dependencies of the provided sources
   */
  def computeDirectDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode]

  /**
   * @param nodesToAnalyze the set of dependency nodes for which the direct dependents should be computed
   * @param includeInfeasibilityNodes if set to true, dependents found via infeasibility nodes are included in the result
   * @param includeUpwardEdges if set to true, interprocedural upward edges are taken into account
   * @param includeDownwardEdges if set to true, interprocedural downward edges are taken into account
   * @return the set of direct dependents of the provided targets
   */
  def computeDirectDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode]

  /**
   * Exports the graph to the folder 'dirName'.
   */
  def exportGraph(dirName: String): Unit
}

class DependencyGraph[T <: DependencyGraphState] extends ReadOnlyDependencyGraph[T] {
  private val edges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val edgesConnectingMethodsDownwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // e.g. edges connecting POSTcondition with method/function calls
  private val edgesConnectingMethodsUpwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // e.g. edges connecting PREconditions with method/function calls
  private var vacuousProofs: mutable.Set[Int] = mutable.Set()

  private val assumptionNodes: mutable.Map[Int, GeneralAssumptionNode] = mutable.HashMap.empty
  private val assertionNodes: mutable.Map[Int, GeneralAssertionNode] = mutable.HashMap.empty

  def getNodes: Set[DependencyAnalysisNode] = getAssumptionNodes ++ getAssertionNodes
  def getAssumptionNodes: Set[GeneralAssumptionNode] = assumptionNodes.values.toSet
  def getAssertionNodes: Set[GeneralAssertionNode] = assertionNodes.values.toSet
  def getIntraMethodEdges: Map[Int, Set[Int]] = edges.toMap
  def getEdgesConnectingMethodsDownwards: Map[Int, Set[Int]] = edgesConnectingMethodsDownwards.toMap
  def getEdgesConnectingMethodsUpwards: Map[Int, Set[Int]] = edgesConnectingMethodsUpwards.toMap

  def getAssumptionNodeById(id: Int): Option[GeneralAssumptionNode] = assumptionNodes.get(id)
  def getAssertionNodeById(id: Int): Option[GeneralAssertionNode] = assertionNodes.get(id)
  def getNodeById(id: Int): Option[DependencyAnalysisNode] = assumptionNodes.get(id).orElse(assertionNodes.get(id))


  def getAllEdges: Map[Int, Set[Int]] = {
    val intraMethodEdges = getIntraMethodEdges
    val keys = intraMethodEdges.keySet ++ edgesConnectingMethodsDownwards.keySet ++ edgesConnectingMethodsUpwards.keySet
    val allEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      allEdges.update(key, intraMethodEdges.getOrElse(key, Set()) ++ edgesConnectingMethodsDownwards.getOrElse(key, Set()) ++ edgesConnectingMethodsUpwards.getOrElse(key, Set()))
    }
    allEdges.toMap
  }

  def getAllEdges(includeDownwardEdges: Boolean, includeUpwardEdges: Boolean): Map[Int, Set[Int]] = {
    val intraMethodEdges = getIntraMethodEdges
    val upwardEdges: mutable.Map[Int, Set[Int]] = if (includeUpwardEdges) edgesConnectingMethodsUpwards else mutable.Map.empty
    val downwardEdges: mutable.Map[Int, Set[Int]]  = if (includeDownwardEdges) edgesConnectingMethodsDownwards else mutable.Map.empty
    val keys = intraMethodEdges.keySet ++ downwardEdges.keySet ++ upwardEdges.keySet
    val allEdges = mutable.Map[Int, Set[Int]]()
    keys foreach {key =>
      allEdges.update(key, intraMethodEdges.getOrElse(key, Set()) ++ downwardEdges.getOrElse(key, Set()) ++ upwardEdges.getOrElse(key, Set()))
    }
    allEdges.toMap
  }

  def getVacuousProofs: Set[Int] = vacuousProofs.toSet // TODO ake: what to do with these?

  def addAssumptionNode(node: GeneralAssumptionNode): Unit = {
    assumptionNodes.update(node.id, node)
  }

  def addAssumptionNodes(newNodes: Iterable[GeneralAssumptionNode]): Unit = {
    newNodes foreach addAssumptionNode
  }

  def addNode(node: DependencyAnalysisNode): Unit = {
    node match {
      case n: GeneralAssertionNode => addAssertionNode(n)
      case n: GeneralAssumptionNode => addAssumptionNode(n)
    }
  }

  def addAssertionNode(node: GeneralAssertionNode): Unit = {
    assertionNodes.update(node.id, node)
  }

  def addAssertionNodes(newNodes: Iterable[GeneralAssertionNode]): Unit = {
    newNodes foreach addAssertionNode
  }

  def addEdges(source: Int, targets: Iterable[Int]): Unit = {
    addEdges(Set(source), targets)
  }

  def addEdges(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edges.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      edges.update(target, oldSources ++ newSources)
  }

  def addEdges(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdges(sources, _))
  }

  def addEdgesConnectingMethodsDownwards(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edgesConnectingMethodsDownwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      edgesConnectingMethodsDownwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsDownwards(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsDownwards(sources, _))
  }

  def addEdgesConnectingMethodsDownwards(source: Int, targets: Iterable[Int]): Unit = {
    addEdgesConnectingMethodsDownwards(Set(source), targets)
  }

  def addEdgesConnectingMethodsUpwards(sources: Iterable[Int], target: Int): Unit = {
    val oldSources = edgesConnectingMethodsUpwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      edgesConnectingMethodsUpwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsUpwards(sources: Iterable[Int], targets: Iterable[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsUpwards(sources, _))
  }

  def addEdgesConnectingMethodsUpwards(source: Int, targets: Iterable[Int]): Unit = {
    addEdgesConnectingMethodsUpwards(Set(source), targets)
  }


  def addVacuousProof(assertionId: Int): Unit = {
    vacuousProofs.add(assertionId)
  }

  def getNodesByIds(targets: Set[Int]): Set[DependencyAnalysisNode] = {
    getNodes.filter(n => targets.contains(n.id))
  }

  def computeDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val infeasibilityNodeIds: Set[Int] = if (includeInfeasibilityNodes) Set.empty else getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)
    val visited: mutable.Set[Int] = mutable.Set.empty
    val queue: mutable.Queue[Int] = mutable.Queue(nodesToAnalyze.map(_.id).toSeq: _*)
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while(queue.nonEmpty) {
      val curr = queue.dequeue()
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds)
      visited.add(curr)
      queue.enqueueAll(newVisits.diff(visited).diff(queue.toSet))
    }
    (visited flatMap getNodeById).toSet
  }

  def computeDirectDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val depIds = nodesToAnalyze.groupBy(_.sourceInfo).flatMap { case (sourceInfo, nodes) =>
      getDirectDependenciesInternal(nodes.map(_.id).toList, sourceInfo, includeInfeasibilityNodes, includeUpwardEdges, includeDownwardEdges)
    }
    (depIds flatMap getNodeById).toSet
  }

  private def getDirectDependenciesInternal(initQueue: List[Int], targetSourceInfo: AnalysisSourceInfo, includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[Int] = {
    val infeasibilityNodeIds: Set[Int] = if (includeInfeasibilityNodes) Set.empty else getAssumptionNodes.filter(_.isInstanceOf[InfeasibilityNode]).map(_.id)
    val targetIds: Set[Int] = initQueue.toSet
    val sourceInfoNodeIds: Set[Int] = getNodes.filter(_.sourceInfo == targetSourceInfo).map(_.id)
    assert(targetIds.subsetOf(sourceInfoNodeIds), s"Target ids do not all belong to sourceInfo $targetSourceInfo")
    val visited: mutable.Set[Int] = mutable.Set.empty
    val result: mutable.Set[Int] = mutable.Set.empty
    var queue: List[Int] = initQueue
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while (queue.nonEmpty) {
      val curr = queue.head
      val newVisits = allEdges.getOrElse(curr, Set()).diff(infeasibilityNodeIds).diff(visited)
      val newQueues = newVisits.intersect(sourceInfoNodeIds)
      visited.addAll(newVisits)
      result.addAll(newVisits.diff(newQueues))
      queue = queue.tail ++ newQueues.diff(queue.toSet)
    }
    result.toSet
  }

  def computeDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val infeasibilityNodeIds: Set[Int] = if (includeInfeasibilityNodes) Set.empty else getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)
    val visited: mutable.Set[Int] = mutable.Set.empty
    var queue: Set[Int] = nodesToAnalyze.map(_.id)
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while(queue.nonEmpty) {
      val newVisits = allEdges.filter{ case (t, s) => s.intersect(queue).nonEmpty && !infeasibilityNodeIds.contains(t) }.keys.toSet
      visited.addAll(queue)
      queue = newVisits.diff(visited)
    }
    (visited flatMap getNodeById).toSet
  }

  def computeDirectDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val infeasibilityNodeIds: Set[Int] = if (includeInfeasibilityNodes) Set.empty else getAssumptionNodes filter (_.isInstanceOf[InfeasibilityNode]) map (_.id)
    val visited: mutable.Set[Int] = mutable.Set.empty
    val result: mutable.Set[Int] = mutable.Set.empty
    var queue: Set[Int] = nodesToAnalyze.map(_.id)
    val sourceSourceInfos = nodesToAnalyze.map(_.sourceInfo)
    val allEdges = getAllEdges(includeDownwardEdges, includeUpwardEdges)
    while(queue.nonEmpty) {
      visited.addAll(queue)
      val newVisits = allEdges.filter{case (t, s) => s.intersect(queue).nonEmpty && !infeasibilityNodeIds.contains(t)}.keys.toSet.diff(visited)
      val newQueues = getNodesByIds(newVisits).filter(n => sourceSourceInfos.contains(n.sourceInfo)).map(_.id)
      result.addAll(newVisits.diff(newQueues))
      queue = newQueues.diff(visited)
    }
    (result flatMap getNodeById).toSet
  }

  /**
   * Removes the provided nodes while perceiving the transitive closure by adding edges between the predecessors and successors.
   */
  private def removeAllEdgesForNode(node: DependencyAnalysisNode): Unit = {
    val id = node.id
    val predecessors = (edges filter { case (_, t) => t.contains(id) }).keys
    val successors = edges.getOrElse(id, Set.empty)
    edges.remove(id)
    predecessors foreach (pid => edges.update(pid, edges.getOrElse(pid, Set.empty).filter(_ != id) ++ successors))
  }


  /**
   * Removes all label nodes while perceiving the transitive closure by adding edges between the predecessors and successors.
   */
  def removeLabelNodes(): Unit = {
    def filterCriteria(n: DependencyAnalysisNode) = n.isInstanceOf[LabelNode]

    val nodesToRemove = getAssumptionNodes filter filterCriteria
    nodesToRemove foreach removeAllEdgesForNode
    removeNodes(nodesToRemove.map(_.id))
  }

  /**
   * Removes internal nodes while perceiving the transitive closure by adding edges between the predecessors and successors.
   */
  def removeInternalNodes(): Unit = {
    def filterCriteria(n: DependencyAnalysisNode) = {
      n.assumptionType.isInstanceOf[AssumptionType.InternalType] && !n.isInstanceOf[InfeasibilityNode]
    }

    val nodesToRemove = getNodes filter filterCriteria
    nodesToRemove foreach removeAllEdgesForNode
    removeNodes(nodesToRemove.map(_.id))
  }

  private def removeNodes(nodeIds: Iterable[Int]) = {
    nodeIds map assumptionNodes.remove
    nodeIds map assertionNodes.remove
  }

  def exportGraph(dirName: String): Unit = {
    val directory = Paths.get(dirName).toFile
    directory.mkdir()
    exportNodes(dirName + "/nodes.csv")
    exportEdges(dirName + "/edges.csv")
  }

  private def exportEdges(fileName: String): Unit = {
    val builder = new StringBuilder()
    getIntraMethodEdges foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",direct" + "\n")))
    getEdgesConnectingMethodsDownwards foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",interprocedural downward" + "\n")))
    getEdgesConnectingMethodsUpwards foreach (e => e._2 foreach (s => builder.append(s.toString + "," + e._1.toString + ",interprocedural upward" + "\n")))

    val writer = new PrintWriter(fileName)
    writer.println("source,target,label")
    writer.println(builder.toString())
    writer.close()
  }

  private def exportNodes(fileName: String): Unit = {
    val sep = "#"
    def getNodeExportString(node: DependencyAnalysisNode): String = {
      val hasFailed = node match {
        case node: GeneralAssertionNode => node.hasFailed
        case _ => false
      }
      val parts = mutable.Seq(node.id.toString, node.getNodeType, node.toString, node.getNodeString, node.sourceInfo.toString,
        node.sourceInfo.getPositionString, node.mergeInfo.toString, node.sourceInfo.getDescription, node.memberStr, hasFailed.toString)
      parts.map(_.replace("#", "@")).mkString(sep)
    }
    val headerParts = mutable.Seq("id", "node type", "assumption type", "node info", "source info", "position", "merge info", "description", "member name", "failed?")
    val builder = new StringBuilder()
    getNodes foreach (n => builder.append(getNodeExportString(n).replace("\n", " ") + "\n"))

    val writer = new PrintWriter(fileName)
    writer.println(headerParts.mkString(sep))
    writer.println(builder.result())
    writer.close()
  }
}


