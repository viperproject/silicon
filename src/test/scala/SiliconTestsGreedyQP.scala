// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

/** Runs a representative subset of the quantified permission tests with the greedy QP exhale
  * algorithm, which also enables tag- and original-condition-based merging of quantified chunks
  * during state consolidation. The pure greedy mode (rather than greedy with fallback to the
  * complete algorithm) is used so that greedy-mode regressions are not masked by the fallback;
  * the tests' annotations reflect the expected behavior of this mode.
  */
class SiliconTestsGreedyQP extends SiliconTests {
  override val testDirectories: Seq[String] = Seq("greedyQP")

  override val commandLineArguments: Seq[String] = Seq(
    "--timeout", "600" /* seconds */,
    "--exhaleModeQP=0")
}
