// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.graph.{AxiomAssumptionNode, DependencyGraphHelper, DependencyNodeFactory, NodeMetadata}
import viper.silicon.state.terms.Term
import viper.silver.dependencyAnalysis.DependencyAnalysisMergeInfo

/**
 * An immutable view of the axiom nodes that exist at some point of a verification run.
 *
 * Axiom nodes are not part of the graphs of the members, which refer to them by id only, and are added once when these
 * graphs are joined. Finalizing the graph of a member still has to treat them like its own nodes, for which it uses
 * the lookups provided here.
 */
final class AxiomNodes private (val nodes: Vector[AxiomAssumptionNode],
                                idsByMergeInfo: Map[DependencyAnalysisMergeInfo, Set[Int]],
                                removableInternalIds: Set[Int]) {

  def idsWithMergeInfo(mergeInfo: DependencyAnalysisMergeInfo): Set[Int] = idsByMergeInfo.getOrElse(mergeInfo, Set.empty)

  def isRemovableInternalNode(id: Int): Boolean = removableInternalIds.contains(id)

  private[dependencyAnalysis] def added(node: AxiomAssumptionNode): AxiomNodes = {
    val newIdsByMergeInfo =
      if (node.mergeInfo.isMerge) idsByMergeInfo.updated(node.mergeInfo, idsWithMergeInfo(node.mergeInfo) + node.id)
      else idsByMergeInfo
    val newRemovableInternalIds =
      if (DependencyGraphHelper.isRemovableInternalNode(node)) removableInternalIds + node.id
      else removableInternalIds
    new AxiomNodes(nodes :+ node, newIdsByMergeInfo, newRemovableInternalIds)
  }
}

object AxiomNodes {
  val empty: AxiomNodes = new AxiomNodes(Vector.empty, Map.empty, Set.empty)
}

/**
 * Creates and stores the axiom nodes of all provers of a verification run.
 * Axioms are emitted while verifiers read the current nodes, hence the registry can be used concurrently.
 */
class AxiomNodeRegistry(options: DependencyAnalysisOptions) {
  @volatile private var _current: AxiomNodes = AxiomNodes.empty

  def current: AxiomNodes = _current

  /** @return the id of the newly created node */
  def addAxiom(assumption: Term, axiomInfo: DependencyAnalysisAxiomInfo, description: Option[String] = None): Int = {
    val analysisInfos = DependencyAnalyzer.checkedInfos(axiomInfo.analysisInfos, axiomInfo.memberStr, options)
    val node = DependencyNodeFactory.createAxiomAssumptionNode(assumption, description, NodeMetadata.forAssumption(analysisInfos, axiomInfo.memberStr))
    synchronized { _current = _current.added(node) }
    node.id
  }
}
