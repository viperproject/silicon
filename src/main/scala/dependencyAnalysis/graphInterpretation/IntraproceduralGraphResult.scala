// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graphInterpretation

import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.interfaces.Failure
import viper.silver.ast
import viper.silver.dependencyAnalysis.JoinType

/**
 * The outcome of analyzing a single member, which is the input for joining the graphs of all members.
 */
class IntraproceduralGraphResult(val graph: ReadOnlyDependencyGraph[IntraProcedural], val errors: List[Failure], val member: ast.Member) {
  private lazy val joinCandidates: Set[DependencyAnalysisNode] = graph.getNodes.filter(_.joinInfos.nonEmpty)

  lazy val joinSinkNodes: Set[DependencyAnalysisNode] = joinCandidates.filter(_.joinInfos.exists(_.joinType.equals(JoinType.Sink)))
  lazy val joinSourceNodes: Set[DependencyAnalysisNode] = joinCandidates.filter(_.joinInfos.exists(_.joinType.equals(JoinType.Source)))
}
