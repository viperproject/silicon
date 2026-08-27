// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

/** Runs a representative subset of the test suite with the maskHeap encoding: core
  * language features, (recursive) predicates, heap-dependent functions and their
  * triggers, quantified permissions over predicates and combinations, magic wands,
  * and some larger examples. The subset is chosen to cover a good combination of
  * features while keeping the suite's runtime moderate.
  */
class SiliconTestsMaskHeapMode extends SiliconTests {
  override val testDirectories: Seq[String] = Seq(
    "all/basic",
    "all/functions",
    "all/inhale_exhale",
    "all/old",
    "all/permissions",
    "examples",
    //"quantifiedpermissions/sets",
    "quantifiedpredicates/basic",
    "quantifiedcombinations",
    //"wands/mwsf"
    "wands/examples")


  override val commandLineArguments: Seq[String] = Seq(
    "--timeout", "300" /* seconds */,
    "--maskHeapMode")
}
