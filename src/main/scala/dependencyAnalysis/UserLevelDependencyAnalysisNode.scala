// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.graph._
import viper.silver.ast.Position
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType
import viper.silver.dependencyAnalysis.{DependencyAnalysisSourceInfo, StringDependencyAnalysisSourceInfo}

object UserLevelDependencyAnalysisNode {

  def from(dependencyNodes: Iterable[DependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
    val res = dependencyNodes
      .map(n => ((StringDependencyAnalysisSourceInfo(n.sourceInfo.getDescription, n.sourceInfo.getPosition), n.memberStr), n))
      .groupBy(_._1).map { case (key, nodes) =>
      UserLevelDependencyAnalysisNode(key._1, key._2, nodes.map(_._2).toSet)
    }.toSet
    res
  }

  def extractByAssumptionType(nodes: Set[UserLevelDependencyAnalysisNode], filterCriteria: AssumptionType => Boolean): Set[UserLevelDependencyAnalysisNode] = {
    nodes.filter(node => node.assumptionTypes exists filterCriteria)
  }

  def mkUserLevelString(nodes: Set[DependencyAnalysisNode], sep: String = "\n"): String = {
    from(nodes).toList.sortBy(n => (n.source.getLineNumber, n.source.toString)).mkString(sep)
  }

  implicit class SetNodeOps(private val left: Set[UserLevelDependencyAnalysisNode]) extends AnyVal {
    def diffBySource(right: Set[UserLevelDependencyAnalysisNode]): Set[UserLevelDependencyAnalysisNode] = {
      val sources = right.map(_.groupingCondition)
      left.filterNot(n => sources.contains(n.groupingCondition))
    }

    def toSourceSet(): Set[DependencyAnalysisSourceInfo] = {
      left.map(_.source)
    }

    def toSourceMemberSet(): Set[(DependencyAnalysisSourceInfo, String)] = {
      left.map(n => (n.source, n.member))
    }
  }
}

case class UserLevelDependencyAnalysisNode(source: DependencyAnalysisSourceInfo, member: String, lowerLevelNodes: Set[DependencyAnalysisNode]) {

  def position: Position = source.getPosition

  def assumptionTypes: Set[AssumptionType] = lowLevelAssumptionNodes.map(_.assumptionType)
  def assertionTypes: Set[AssumptionType] = lowLevelAssertionNodes.map(_.assumptionType)

  lazy val lowLevelAssumptionNodes: Set[GeneralAssumptionNode] = lowerLevelNodes.collect { case node: GeneralAssumptionNode => node }
  lazy val lowLevelAssertionNodes: Set[GeneralAssertionNode] = lowerLevelNodes.collect { case node: GeneralAssertionNode => node }

  lazy val hasFailures: Boolean = lowLevelAssertionNodes.exists(_.hasFailed)

  override def toString: String = source.toString

  def groupingCondition: (String, Position) = (source.toString, position)

}

case class CompactUserLevelDependencyAnalysisNode(source: DependencyAnalysisSourceInfo, assumptionTypes: Set[AssumptionType], assertionTypes: Set[AssumptionType], hasFailures: Boolean) {
  def position: Position = source.getPosition
}
