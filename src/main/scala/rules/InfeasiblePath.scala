// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.rules

import viper.silicon.decider.RecordedPathConditions
import viper.silicon.dependencyAnalysis.AnalysisInfos
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.parser.PUnknown

/**
 * Defines what the symbolic execution rules do on an infeasible path, i.e. a path whose path conditions are contradictory.
 *
 * By default, verification stops on such a path. If infeasible paths are explored, which the dependency analysis needs in
 * order to record the dependencies of the path's remaining proof obligations, verification continues until the end of
 * the path instead. The rules only state how they would continue; whether they do is decided here.
 */
object infeasiblePath extends SymbolicExecutionRules {
  private def isExplored: Boolean = Verifier.config.analyzeInfeasiblePaths

  /** True if verification stops on an infeasible path. Rules that do not have to prove a path infeasible can skip the check if false. */
  def stopsEarly: Boolean = !isExplored

  def exploresBranch(isFeasible: Boolean): Boolean = isFeasible || isExplored

  /** True if the data of a path with the given path conditions must be joined. Infeasible paths do not contribute if they are explored. */
  def contributesToJoin(pathConditions: RecordedPathConditions): Boolean =
    !isExplored || pathConditions.infeasibilityNodeId.isEmpty

  /**
   * Checks whether the current path is known to be infeasible and the rule can therefore skip its usual work.
   * If so, records what the rule would have contributed to the dependency analysis.
   */
  def skipRule(v: Verifier, hasAssertions: => Boolean, hasAssumptions: Boolean, analysisInfos: => AnalysisInfos): Boolean = {
    val skip = v.decider.isPathMarkedInfeasible
    if (skip) v.decider.handleInfeasiblePath(hasAssertions, hasAssumptions, analysisInfos)
    skip
  }

  /**
   * Handles a path that was just proven infeasible.
   *
   * @param stopped the result if verification stops on the path
   * @param alwaysContinue if true, continues even if infeasible paths are not explored
   */
  def continue(stopped: => VerificationResult, alwaysContinue: Boolean = false)(continuation: => VerificationResult): VerificationResult =
    if (alwaysContinue || isExplored) continuation else stopped

  /** Handles a failure that may be reported, and explores the rest of the path if further errors are wanted and infeasible paths are explored. */
  def continueAfterFailure(failure: VerificationResult, s: State, v: Verifier)(continuation: => VerificationResult): VerificationResult =
    if (s.retryLevel == 0 && v.reportFurtherErrors() && isExplored) failure combine continuation else failure

  /** A snapshot for `resource` to continue with, for when an infeasible path has no chunk to provide the actual one. */
  def freshSnapshot(resource: ast.Resource, s: State, v: Verifier): Term =
    v.decider.fresh(v.snapshotSupporter.optimalSnapshotSort(resource, s, v), Option.when(debugOn)(PUnknown()))
}
