// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces._
import viper.silicon.decider.Decider
import viper.silicon.rules.{executionFlowController, executor}
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.state.State.OldHeaps
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silver.cfg.silver.SilverCfg

trait CfgVerificationUnit extends VerificationUnit[SilverCfg]

trait DefaultCfgVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider

  object cfgSupporter extends CfgVerificationUnit with StatefulComponent {
    import executor._

    private var _units: Seq[SilverCfg] = _

    def analyze(program: ast.Program): Unit = {
      ???
    }

    def units = _units

    def verify(sInit: State, cfg: SilverCfg): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " CFG " + "-" * 10 + "\n")
      decider.prover.comment("%s CFG %s".format("-" * 10, "-" * 10))

//      SymbExLogger.insertMember(method, null, v.decider.pcs) TODO: Enable this.

      val g = Store()

      val s = sInit.copy(g = g,
        h = Heap(),
        oldHeaps = OldHeaps(),
        methodCfg = cfg)  // TODO: ???

      if (Verifier.config.printMethodCFGs()) {
        viper.silicon.common.io.toFile(
          cfg.toDot,
          new java.io.File(s"${Verifier.config.tempDirectory()}/CFG${System.identityHashCode(cfg)}.dot"))
      }

      val result = {
        executionFlowController.locally(s, v)((s3, v3) =>  {
          exec(s3, cfg, v3)((_, _) =>
            Success())}) }

      Seq(result)
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop() {}
  }
}
