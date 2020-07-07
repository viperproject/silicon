// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import viper.silver.components.StatefulComponent
import viper.silicon.supporters._
import viper.silver.plugin.PluginAwareReporter

class SlaveVerifier(master: MasterVerifier,
                    uniqueId: String,
                    override val reporter: PluginAwareReporter)
    extends BaseVerifier(Verifier.config, uniqueId)
       with DefaultMethodVerificationUnitProvider
       with DefaultCfgVerificationUnitProvider {

  private val statefulSubcomponents = List[StatefulComponent](
    methodSupporter,
    cfgSupporter
  )

  def verificationPoolManager: VerificationPoolManager = master.verificationPoolManager

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }
}
