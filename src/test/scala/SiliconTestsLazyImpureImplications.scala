// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.tests

import viper.silver.testing.AnnotatedTestInput

class SiliconTestsLazyImpureImplications extends SiliconTests {
  /* Moving the guard of an impure implication into the permission amount has the same consequences
   * as the syntactic transformation performed by --conditionalizePermissions, and the three files
   * below are excluded for the same reasons. All three behave identically under
   * --conditionalizePermissions. */
  val excludedFiles = Set(
    /* Greedy exhale picks a single chunk and cannot sum permissions across chunks that only alias
     * conditionally, so `acc(x.val) && (x != y ==> acc(y.val))` no longer suffices to write y.val.
     * Verifies with --exhaleMode=1. */
    "all/issues/silicon/0324.vpr",
    /* Same, inside a package statement; here --exhaleMode=1 does not help either. */
    "wands/regression/PackageStateConsolidation.vpr",
    /* Not a regression: the test's annotations no longer match because the optimization *removes*
     * two errors annotated as spurious (silicon issue 114) and *reports* one annotated as missing
     * (silicon issue 34). Producing `predicate P(x, b) { b ==> acc(x.f) }` without branching is
     * what makes the difference. */
    "all/issues/silicon/0114.vpr"
  )

  override def isTestToBeIncluded(testInput: AnnotatedTestInput): Boolean = {
    super.isTestToBeIncluded(testInput) && !excludedFiles.contains(testInput.name)
  }

  override val commandLineArguments: Seq[String] = Seq(
    "--timeout", "300" /* seconds */,
    "--lazyImpureImplications")
}
