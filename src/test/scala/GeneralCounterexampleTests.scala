// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.testing.{CounterexampleTestInput, DefaultAnnotatedTestInput}

import java.nio.file.Path

class GeneralCounterexampleTests extends SiliconTests {
  override val testDirectories: Seq[String] = Seq("counterexamples")

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val args = Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap(configMap).getOrElse("silicon", Map()))
    val additionalArgs = Seq("--counterexample", "extended")

    silicon.parseCommandLine(args ++ additionalArgs :+ Silicon.dummyInputFilename)
  }

  override def buildTestInput(file: Path, prefix: String): DefaultAnnotatedTestInput =
    CounterexampleTestInput(file, prefix)
}
