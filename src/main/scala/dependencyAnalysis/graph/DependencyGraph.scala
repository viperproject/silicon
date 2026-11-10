// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graph

import viper.silver.dependencyAnalysis.{AssumptionType, DependencyAnalysisSourceInfo}

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

  /**
   * @return whether the node is removed from the final graph of a member, unless debugging is enabled.
   */
  def isRemovableInternalNode(node: DependencyAnalysisNode): Boolean = node match {
    case _: InfeasibilityNode => false // infeasibility nodes are required for some of the graph queries
    case _ =>
      node.assumptionType.isInstanceOf[AssumptionType.InternalType] &&
        node.joinInfos.isEmpty // join nodes must not be removed because we need them for joining the graphs later on
  }
}

sealed trait DependencyGraphState
class Init extends DependencyGraphState
class IntraProcedural extends DependencyGraphState
class Final extends DependencyGraphState

trait ReadOnlyDependencyGraph[T <: DependencyGraphState] {
  def getNodes: Set[DependencyAnalysisNode]
  def getAssumptionNodes: Set[GeneralAssumptionNode]
  def getAssertionNodes: Set[GeneralAssertionNode]

  def getNodeById(id: Int): Option[DependencyAnalysisNode]
  def getNodesByIds(targets: Set[Int]): Set[DependencyAnalysisNode]

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
  private val intraMethodEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty
  private val edgesConnectingMethodsDownwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // e.g. edges connecting POSTcondition with method/function calls
  private val edgesConnectingMethodsUpwards: mutable.Map[Int, Set[Int]] = mutable.Map.empty // e.g. edges connecting PREconditions with method/function calls
  private val allEdges: mutable.Map[Int, Set[Int]] = mutable.Map.empty // should contain exactly all edges from intraMethodEdges, edgesConnectingMethodsDownwards, edgesConnectingMethodsUpwards
  // TODO ake: collect vacuous proof information
  // private val vacuousProofs: mutable.Set[Int] = mutable.Set()

  private val assumptionNodes: mutable.Map[Int, GeneralAssumptionNode] = mutable.HashMap.empty
  private val assertionNodes: mutable.Map[Int, GeneralAssertionNode] = mutable.HashMap.empty

  def getNodes: Set[DependencyAnalysisNode] = getAssumptionNodes ++ getAssertionNodes
  def getAssumptionNodes: Set[GeneralAssumptionNode] = assumptionNodes.values.toSet
  def getAssertionNodes: Set[GeneralAssertionNode] = assertionNodes.values.toSet

  def getIntraMethodEdges: Map[Int, Set[Int]] = intraMethodEdges.toMap
  def getEdgesConnectingMethodsDownwards: Map[Int, Set[Int]] = edgesConnectingMethodsDownwards.toMap
  def getEdgesConnectingMethodsUpwards: Map[Int, Set[Int]] = edgesConnectingMethodsUpwards.toMap

  def getNodeById(id: Int): Option[DependencyAnalysisNode] = assumptionNodes.get(id).orElse(assertionNodes.get(id))

  def getNodesByIds(targets: Set[Int]): Set[DependencyAnalysisNode] = {
    targets flatMap getNodeById
  }

  def getAllEdges: Map[Int, Set[Int]] = {
    allEdges.toMap
  }

  def getAllEdges(includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Map[Int, Set[Int]] = {
    selectEdges(includeUpwardEdges, includeDownwardEdges).toMap
  }

  /**
   * @return the selected edges as a map from node to its direct dependencies. The result may be the graph's internal
   *         map rather than a copy, so it must only be used for reading and only while the graph is not modified.
   */
  private def selectEdges(includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): collection.Map[Int, Set[Int]] = {
    if (includeDownwardEdges && includeUpwardEdges) allEdges
    else if (!includeDownwardEdges && !includeUpwardEdges) intraMethodEdges
    else {
      val interproceduralEdges = if (includeDownwardEdges) edgesConnectingMethodsDownwards else edgesConnectingMethodsUpwards
      val merged = mutable.Map.from(intraMethodEdges)
      interproceduralEdges foreach { case (target, sources) =>
        merged.update(target, merged.getOrElse(target, Set.empty) ++ sources)
      }
      merged
    }
  }

  private def reverseEdges(edges: collection.Map[Int, Set[Int]]): collection.Map[Int, Set[Int]] = {
    val reversed = mutable.Map.empty[Int, Set[Int]]
    edges foreach { case (target, sources) =>
      sources foreach (source => reversed.update(source, reversed.getOrElse(source, Set.empty) + target))
    }
    reversed
  }

  private def infeasibilityNodeIdsToSkip(includeInfeasibilityNodes: Boolean): Set[Int] = {
    if (includeInfeasibilityNodes) Set.empty
    else assumptionNodes.valuesIterator.collect { case node: InfeasibilityNode => node.id }.toSet
  }

  /**
   * @return startIds and all nodes reachable from them via the given edges without entering a node in skippedIds
   */
  private def computeReachableIds(startIds: Set[Int], edges: collection.Map[Int, Set[Int]], skippedIds: Set[Int]): Set[Int] = {
    val visited = mutable.Set.from(startIds)
    val queue = mutable.Queue.from(startIds)
    while (queue.nonEmpty) {
      edges.getOrElse(queue.dequeue(), Set.empty) foreach { next =>
        if (!skippedIds.contains(next) && visited.add(next)) queue.enqueue(next)
      }
    }
    visited.toSet
  }

  // TODO ake: collect vacuous proof information
  // def getVacuousProofs: Set[Int] = vacuousProofs.toSet

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

  def addEdges(source: Int, targets: Set[Int]): Unit = {
    addEdges(Set(source), targets)
  }

  def addEdges(sources: Set[Int], target: Int): Unit = {
    addToAllEdges(sources, target)
    val oldSources = intraMethodEdges.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      intraMethodEdges.update(target, oldSources ++ newSources)
  }

  private def addToAllEdges(sources: Set[Int], target: Int): Unit = {
    val oldSources = allEdges.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      allEdges.update(target, oldSources ++ newSources)
  }

  def addEdges(sources: Set[Int], targets: Set[Int]): Unit = {
    targets foreach (addEdges(sources, _))
  }

  def addEdgesConnectingMethodsDownwards(sources: Set[Int], target: Int): Unit = {
    addToAllEdges(sources, target)
    val oldSources = edgesConnectingMethodsDownwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      edgesConnectingMethodsDownwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsDownwards(sources: Set[Int], targets: Set[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsDownwards(sources, _))
  }

  def addEdgesConnectingMethodsDownwards(source: Int, targets: Set[Int]): Unit = {
    addEdgesConnectingMethodsDownwards(Set(source), targets)
  }

  def addEdgesConnectingMethodsUpwards(sources: Set[Int], target: Int): Unit = {
    addToAllEdges(sources, target)
    val oldSources = edgesConnectingMethodsUpwards.getOrElse(target, Set.empty)
    val newSources = sources.filter(_ != target)
    if (newSources.nonEmpty)
      edgesConnectingMethodsUpwards.update(target, oldSources ++ newSources)
  }

  def addEdgesConnectingMethodsUpwards(sources: Set[Int], targets: Set[Int]): Unit = {
    targets foreach (addEdgesConnectingMethodsUpwards(sources, _))
  }

  def addEdgesConnectingMethodsUpwards(source: Int, targets: Set[Int]): Unit = {
    addEdgesConnectingMethodsUpwards(Set(source), targets)
  }


  // TODO ake: collect vacuous proof information
  // def addVacuousProof(assertionId: Int): Unit = {
  //   vacuousProofs.add(assertionId)
  // }

  def computeDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val edges = selectEdges(includeUpwardEdges, includeDownwardEdges)
    getNodesByIds(computeReachableIds(nodesToAnalyze.map(_.id), edges, infeasibilityNodeIdsToSkip(includeInfeasibilityNodes)))
  }

  def computeDirectDependencies(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val infeasibilityNodeIds = infeasibilityNodeIdsToSkip(includeInfeasibilityNodes)
    val edges = selectEdges(includeUpwardEdges, includeDownwardEdges)
    val targetsBySourceInfo = nodesToAnalyze.groupBy(_.sourceInfo)
    val nodeIdsBySourceInfo = (assumptionNodes.valuesIterator ++ assertionNodes.valuesIterator)
      .filter(node => targetsBySourceInfo.contains(node.sourceInfo))
      .toList.groupMap(_.sourceInfo)(_.id)
    val depIds = targetsBySourceInfo.flatMap { case (sourceInfo, nodes) =>
      getDirectDependenciesInternal(nodes.map(_.id).toList, sourceInfo, nodeIdsBySourceInfo.getOrElse(sourceInfo, List.empty).toSet, infeasibilityNodeIds, edges)
    }
    (depIds flatMap getNodeById).toSet
  }

  private def getDirectDependenciesInternal(initQueue: List[Int], targetSourceInfo: DependencyAnalysisSourceInfo, sourceInfoNodeIds: Set[Int], infeasibilityNodeIds: Set[Int], edges: collection.Map[Int, Set[Int]]): Set[Int] = {
    assert(initQueue.toSet.subsetOf(sourceInfoNodeIds), s"Target ids do not all belong to sourceInfo $targetSourceInfo")
    val visited: mutable.Set[Int] = mutable.Set.empty
    val result: mutable.Set[Int] = mutable.Set.empty
    val queued: mutable.Set[Int] = mutable.Set.from(initQueue)
    val queue: mutable.Queue[Int] = mutable.Queue.from(initQueue)
    while (queue.nonEmpty) {
      val newVisits = edges.getOrElse(queue.dequeue(), Set.empty).diff(infeasibilityNodeIds).diff(visited)
      val newQueues = newVisits.intersect(sourceInfoNodeIds)
      visited.addAll(newVisits)
      result.addAll(newVisits.diff(newQueues))
      newQueues foreach (id => if (queued.add(id)) queue.enqueue(id))
    }
    result.toSet
  }

  def computeDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val dependents = reverseEdges(selectEdges(includeUpwardEdges, includeDownwardEdges))
    getNodesByIds(computeReachableIds(nodesToAnalyze.map(_.id), dependents, infeasibilityNodeIdsToSkip(includeInfeasibilityNodes)))
  }

  def computeDirectDependents(nodesToAnalyze: Set[DependencyAnalysisNode], includeInfeasibilityNodes: Boolean, includeUpwardEdges: Boolean, includeDownwardEdges: Boolean): Set[DependencyAnalysisNode] = {
    val infeasibilityNodeIds = infeasibilityNodeIdsToSkip(includeInfeasibilityNodes)
    val visited: mutable.Set[Int] = mutable.Set.empty
    val result: mutable.Set[Int] = mutable.Set.empty
    var queue: Set[Int] = nodesToAnalyze.map(_.id)
    val sourceSourceInfos = nodesToAnalyze.map(_.sourceInfo)
    val dependents = reverseEdges(selectEdges(includeUpwardEdges, includeDownwardEdges))
    while(queue.nonEmpty) {
      visited.addAll(queue)
      val newVisits = queue.flatMap(id => dependents.getOrElse(id, Set.empty[Int])).diff(infeasibilityNodeIds).diff(visited)
      val newQueues = getNodesByIds(newVisits).filter(n => sourceSourceInfos.contains(n.sourceInfo)).map(_.id)
      result.addAll(newVisits.diff(newQueues))
      queue = newQueues.diff(visited)
    }
    (result flatMap getNodeById).toSet
  }

  /**
   * Removes the provided nodes from all edge maps while preserving the transitive closure of the remaining nodes:
   * an edge to a removed node is replaced by edges to all remaining nodes reachable via removed nodes only.
   */
  private def removeAllEdgesForNodes(nodeIds: Set[Int]): Unit = {
    def removeEdgesFromMap(edges: mutable.Map[Int, Set[Int]]): Unit = {
      val edgesOfRemovedNodes = edges.view.filterKeys(nodeIds.contains).toMap
      val remainingSuccessors = mutable.Map.empty[Int, Set[Int]]

      def computeRemainingSuccessors(removedId: Int): Set[Int] = remainingSuccessors.getOrElseUpdate(removedId, {
        val result = mutable.Set.empty[Int]
        val visited = mutable.Set(removedId)
        val workList = mutable.Stack(removedId)
        while (workList.nonEmpty) {
          edgesOfRemovedNodes.getOrElse(workList.pop(), Set.empty[Int]) foreach { successor =>
            if (!nodeIds.contains(successor)) result.add(successor)
            else remainingSuccessors.get(successor) match {
              case Some(known) => result.addAll(known)
              case None => if (visited.add(successor)) workList.push(successor)
            }
          }
        }
        result.toSet
      })

      edges --= nodeIds
      edges mapValuesInPlace { (_, successors) =>
        val (removed, remaining) = successors.partition(nodeIds.contains)
        if (removed.isEmpty) successors else remaining ++ removed.flatMap(computeRemainingSuccessors)
      }
    }

    removeEdgesFromMap(intraMethodEdges)
    removeEdgesFromMap(edgesConnectingMethodsDownwards)
    removeEdgesFromMap(edgesConnectingMethodsUpwards)
    removeEdgesFromMap(allEdges)
  }


  /**
   * Removes all label nodes while perceiving the transitive closure by adding edges between the predecessors and successors.
   */
  def removeLabelNodes(): Unit = {
    val idsToRemove = assumptionNodes.valuesIterator.collect { case n: LabelNode => n.id }.toSet
    removeAllEdgesForNodes(idsToRemove)
    removeNodes(idsToRemove)
  }

  /**
   * Removes internal nodes while perceiving the transitive closure by adding edges between the predecessors and successors.
   *
   * @param isExternalInternalNode identifies internal nodes that edges refer to, but that are not part of this graph
   */
  def removeInternalNodes(isExternalInternalNode: Int => Boolean = _ => false): Unit = {
    val externalIdsToRemove = (allEdges.keysIterator ++ allEdges.valuesIterator.flatten).filter(isExternalInternalNode).toSet
    val idsToRemove = getNodes.filter(DependencyGraphHelper.isRemovableInternalNode).map(_.id) ++ externalIdsToRemove
    removeAllEdgesForNodes(idsToRemove)
    removeNodes(idsToRemove)
  }

  private def removeNodes(nodeIds: Iterable[Int]) = {
    nodeIds map assumptionNodes.remove
    nodeIds map assertionNodes.remove
  }

  def exportGraph(dirName: String): Unit = {
    val directory = Paths.get(dirName).toFile
    directory.mkdirs()
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


