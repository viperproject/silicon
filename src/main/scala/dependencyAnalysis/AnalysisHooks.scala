// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.graph.DependencyAnalysisNode
import viper.silicon.state.terms.Term
import viper.silver.ast

/**
 * The interface through which verification code reports to an analysis. Every method does nothing by default, which
 * is the behaviour of a run without an analysis.
 */
trait AnalysisHooks {
  /** Starts analyzing the given member. The preamble nodes describe axioms emitted to the provers of all verifiers. */
  def beginMember(member: ast.Member, preambleNodes: Iterable[DependencyAnalysisNode]): Unit = {}

  def endMember(): Unit = {}

  /**
   * Called when symbolic execution reaches an AST node.
   *
   * @return the infos to use while processing the node. Additional dependency nodes requested by `info` are recorded
   *         as a side effect.
   */
  def enterNode(analysisInfos: AnalysisInfos, info: ast.Info, node: ast.Node): AnalysisInfos = analysisInfos

  /** @return the term, guarded by a fresh label that depends on the given nodes if the analysis tracks them */
  def withLabel(term: Term, sourceNodeIds: Set[Int] = Set.empty): Term = term

  /**
   * @return the node of the most recent `Decider.check` if that check succeeded and created one. Must be read before
   *         the next check, which replaces it.
   */
  def lastCheckNodeIds: Set[Int] = Set.empty

  /** Connects all nodes with a merge info in `sourceExps` to all nodes with a merge info in `targetExps`. */
  def linkMergeInfos(sourceExps: Seq[ast.Exp], targetExps: Seq[ast.Exp]): Unit = {}

  def recordAssumption(assumption: Term, analysisInfos: AnalysisInfos, description: Option[String] = None): Unit = {}
}

object NoAnalysisHooks extends AnalysisHooks
