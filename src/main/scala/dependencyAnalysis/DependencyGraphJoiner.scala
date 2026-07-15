// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.SiliconRunner
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.verifier.Verifier
import viper.silver.dependencyAnalysis.EdgeType.EdgeType
import viper.silver.dependencyAnalysis.JoinType.JoinType
import viper.silver.dependencyAnalysis.{DependencyAnalysisSourceInfo, EdgeType, JoinType}

import scala.collection.mutable

/**
 * * @param name Optional name for the joined graph.
 * * @param dependencyGraphInterpreters The graphs to be joined.
 */
class DependencyGraphJoiner(name: String, dependencyGraphInterpreters: Set[DependencyGraphInterpreter[IntraProcedural]]) {

  /**
   * @return A dependency graph interpreter operating on a new dependency graph that represents all input graphs and
   *         all dependencies between them.
   * The new graph is built by adding all existing nodes and edges of all input graphs and joining them
   * via the join information stored in each node.
   */
  def joinGraphsAndGetInterpreter(): DependencyGraphInterpreter[Final] = {
    SiliconRunner.logger.info(s"INFO: Joining all graphs...")
    val newGraph = new DependencyGraph[Final]

    SiliconRunner.logger.info(s"INFO: Copying nodes...")
    newGraph.addAssumptionNodes(dependencyGraphInterpreters.flatMap (_.getAssumptionNodes))
    newGraph.addAssertionNodes(dependencyGraphInterpreters.flatMap (_.getAssertionNodes))
    SiliconRunner.logger.info(s"INFO: Copying edges...")
    dependencyGraphInterpreters foreach (interpreter => interpreter.getGraph.getAllEdges foreach {case (t, deps) => newGraph.addEdges(deps, t)})

    val joinSourceNodes = dependencyGraphInterpreters flatMap(i => i.joinSourceNodes)
    val joinSinkNodes   = dependencyGraphInterpreters flatMap(i => i.joinSinkNodes)

    def getJoinNodesByJoinInfo(candidateNodes: Set[DependencyAnalysisNode], joinType: JoinType): Map[(DependencyAnalysisSourceInfo, EdgeType), Set[DependencyAnalysisNode]] = {
      val acc: mutable.Map[(DependencyAnalysisSourceInfo, EdgeType), Set[DependencyAnalysisNode]] = mutable.Map.empty
      candidateNodes.foreach {
        node =>
          node.joinInfos.foreach { joinInfo =>
            if (joinInfo.joinType.equals(joinType)) {
              val key = (joinInfo.sourceInfo, joinInfo.edgeType)
              acc.update(key, acc.getOrElse(key, Set.empty) + node)
            }
          }
      }
      acc.toMap
    }

    SiliconRunner.logger.info(s"INFO: GetJoinNodesByJoinInfo...")
    val sourceNodesByJoinInfo = getJoinNodesByJoinInfo(joinSourceNodes, JoinType.Source)
    val sinkNodesByJoinInfo = getJoinNodesByJoinInfo(joinSinkNodes, JoinType.Sink)

    val sourceInfoToNodeIds = newGraph.getNodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.id)).toMap

    SiliconRunner.logger.info(s"INFO: Adding join edges...")
    sinkNodesByJoinInfo.foreach { case (joinKey, sinkNodes) =>
      val matchingSourceNodes = sourceNodesByJoinInfo.getOrElse(joinKey, Set.empty)
      addEdgesConnectingMethods(newGraph, joinKey._2, matchingSourceNodes, sinkNodes, sourceInfoToNodeIds)
    }

    val newInterpreter = new DependencyGraphInterpreter[Final](name, newGraph, dependencyGraphInterpreters.toList.flatMap(_.getErrors))
    SiliconRunner.logger.info(s"INFO: Finished joining all graphs.")
    newInterpreter
  }

  private def addEdgesConnectingMethods(newGraph: DependencyGraph[Final], edgeType: EdgeType, sourceNodes: Set[DependencyAnalysisNode], sinkNodes: Set[DependencyAnalysisNode], sourceInfoToNodeIds: Map[DependencyAnalysisSourceInfo, Set[Int]]): Unit = {
    if (edgeType.equals(EdgeType.Up)) {
      val directDepsOfSources = if(!Verifier.config.disableDependencyAnalysisJoinPrecisionOpt()) {
        // Preconditions are connected to the dependencies required to prove them at all call sites. However, they do not depend on the calls themselves.
        sourceNodes.groupBy(_.sourceInfo).flatMap(t => getDirectIntraMethodDependencies(t._2.map(_.id), sourceInfoToNodeIds(t._1), newGraph))
      } else {
        // Connect preconditions directly to call and therefore, indirectly to all its dependencies -> imprecise but might be faster and
        // more user-friendly since it becomes apparent which call introduced these indirect dependencies.
        sourceNodes.map(_.id)
      }
      newGraph.addEdgesConnectingMethodsUpwards(directDepsOfSources, sinkNodes.map(_.id))
    } else {
      newGraph.addEdgesConnectingMethodsDownwards(sourceNodes.map(_.id), sinkNodes.map(_.id))
    }
  }

  private def getDirectIntraMethodDependencies(initQueue: Set[Int], allNodesWithSameSource: Set[Int], graph: DependencyGraph[Final]): Set[Int] = {
    assert(initQueue.subsetOf(allNodesWithSameSource), s"Target ids do not all belong to sourceInfo $allNodesWithSameSource")
    val visited: mutable.Set[Int] = mutable.Set.empty
    val result: mutable.Set[Int] = mutable.Set.empty
    val queue: mutable.Queue[Int] = mutable.Queue(initQueue.toSeq: _*)
    val relevantEdges = graph.
      getIntraMethodEdges
    while (queue.nonEmpty) {
      val curr = queue.dequeue()
      val newVisits = relevantEdges.getOrElse(curr, Set()).diff(visited)
      val newQueues = newVisits.intersect(allNodesWithSameSource)
      visited.addAll(newVisits)
      result.addAll(newVisits.diff(newQueues))
      queue.enqueueAll(newQueues.diff(queue.toSet))
    }
    result.toSet
  }
}
