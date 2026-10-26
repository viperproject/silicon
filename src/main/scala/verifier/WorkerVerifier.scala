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
                     override val reporter: Reporter,
                     override val debugMode: Boolean)
    extends BaseVerifier(Verifier.config, uniqueId)
       with DefaultMethodVerificationUnitProvider
       with DefaultCfgVerificationUnitProvider {

  private val statefulSubcomponents = List[StatefulComponent](
    methodSupporter,
    cfgSupporter
  )

  def verificationPoolManager: VerificationPoolManager = mainVerifier.verificationPoolManager

  /** False for the verifiers a debug session uses to work with a proof obligation: what they execute must not be
    * paused or reported as a failure of the verification, which would block the session's own thread. */
  @volatile var debugHookEnabled: Boolean = true

  override def debugHook: Option[viper.silicon.debugger.DebugHook] =
    if (debugHookEnabled) mainVerifier.debugHook else None

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
