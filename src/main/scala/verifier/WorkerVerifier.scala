// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import viper.silicon.supporters._
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.reporter.Reporter

class WorkerVerifier(mainVerifier: MainVerifier,
                     uniqueId: String,
                     override val reporter: Reporter)
    extends BaseVerifier(Verifier.config, uniqueId)
       with DefaultMethodVerificationUnitProvider
       with DefaultCfgVerificationUnitProvider {

  private val statefulSubcomponents = List[StatefulComponent](
    methodSupporter,
    cfgSupporter
  )

  def verificationPoolManager: VerificationPoolManager = mainVerifier.verificationPoolManager

  override def openSymbExLogger(member: ast.Member): Unit = {
    symbExLog = mainVerifier.rootSymbExLogger.openMemberScope(member, decider.pcs)
  }

  /* Lifetime */

  override def start(): Unit = {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset(): Unit = {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop(): Unit = {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }
}
