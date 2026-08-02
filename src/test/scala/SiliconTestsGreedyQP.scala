// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import viper.silver.testing.AnnotatedTestInput

/** Runs the quantified permission tests with the greedy QP exhale algorithm (with fallback to the
  * standard complete algorithm on failure, i.e. exhaleModeQP 2), which also enables tag- and
  * original-condition-based merging of quantified chunks during state consolidation.
  */
class SiliconTestsGreedyQP extends SiliconTests {
  // TODO: Restrict to a smaller, representative subset of the QP tests to keep overall
  //       test suite runtime reasonable.
  override val testDirectories: Seq[String] =
    Seq("quantifiedpermissions", "quantifiedpredicates", "quantifiedcombinations")

  override val commandLineArguments: Seq[String] = Seq(
    "--timeout", "600" /* seconds */,
    "--exhaleModeQP=2")

  /* Tests whose expected outputs deviate under the greedy algorithm:
   *  - issue_0184.vpr: the known incompleteness (Silicon issue 184) is resolved by the greedy
   *    modes' chunk merging during state consolidation, so the file's UnexpectedOutput annotation
   *    does not apply here.
   *  - misc1.vpr: known incompleteness of the greedy algorithm (spurious insufficient-permission
   *    error that the fallback to the complete algorithm does not currently avoid).
   */
  private val knownDeviations = Set(
    "quantifiedpermissions/issues/issue_0184.vpr",
    "quantifiedpermissions/misc/misc1.vpr")

  override protected def isTestToBeIncluded(testInput: AnnotatedTestInput): Boolean =
    super.isTestToBeIncluded(testInput) &&
      !knownDeviations.exists(d => testInput.files.head.toString.replace('\\', '/').endsWith(d))
}
