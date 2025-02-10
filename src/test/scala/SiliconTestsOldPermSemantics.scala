// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

class SiliconTestsOldPermSemantics extends SiliconTests {
  override val testDirectories: Seq[String] = Seq("oldpermsemantics")

 override val commandLineArguments: Seq[String] = Seq(
    "--timeout", "300" /* seconds */,
    "--respectFunctionPrePermAmounts")
}
