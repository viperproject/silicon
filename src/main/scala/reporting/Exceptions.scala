// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import viper.silver.ast
import viper.silver.verifier.AbstractError

trait SiliconException extends RuntimeException {
  def asViperError: AbstractError
}

case class ExternalToolError(tool: String, message: String)
    extends RuntimeException(message)
       with SiliconException {

  val asViperError = new AbstractError {
    def pos = ast.NoPosition
    def fullId = "external.tool.error"
    def readableMessage = s"Problem with external tool $tool: $message"
  }
}

case class ProverInteractionFailed(proverId: String, message: String)
    extends RuntimeException(message)
        with SiliconException {

  val asViperError = new AbstractError {
    def pos = ast.NoPosition
    def fullId = "prover.interaction.failed"
    def readableMessage = s"Interaction with prover (instance $proverId) failed: $message"
  }
}
