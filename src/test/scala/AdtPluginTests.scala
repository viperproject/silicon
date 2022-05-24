// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.


package viper.silicon.tests

import viper.silicon.Silicon
import viper.silver.reporter.NoopReporter


class AdtPluginTests extends SiliconTests {

  override val testDirectories: Seq[String] = Seq("adt")

  override val silicon: Silicon = {
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.AdtPluginTests") :: Nil
    new Silicon(reporter, debugInfo)
  }

  override def verifiers = List(silicon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    val newConfigMap = configMap.updated("silicon:plugin", "viper.silver.plugin.standard.adt.AdtPlugin")
    super.configureVerifiersFromConfigMap(newConfigMap)
  }

}
