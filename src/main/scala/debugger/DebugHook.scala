// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.interfaces.Failure
import viper.silicon.state.State
import viper.silicon.verifier.{MainVerifier, Verifier}
import viper.silver.ast
import viper.silver.verifier.ExtensionAbstractErrorReason
import viper.silver.verifier.errors.ErrorNode

/**
  * Lets a debugger observe, and pause, the symbolic execution of a program. A hook is installed with
  * [[viper.silicon.Silicon.debugHook_=]]; [[DebugRunController]] is the implementation that supports breakpoints.
  *
  * The methods are called on the thread of the verifier that executes the program. They may block it for as
  * long as the verification should be paused, and they may throw [[DebugRunAborted]] to end the verification.
  */
trait DebugHook {

  /** Called once per verification, before any member is verified, with the program as it is executed. */
  def verificationStarted(program: ast.Program, mainVerifier: MainVerifier): Unit

  /** Called before verifier `v` executes `stmt` in state `s`. */
  def beforeExec(s: State, stmt: ast.Stmt, v: Verifier): Unit

  /**
    * Called when verifier `v` reports `failure` in state `s`. Only final failures are reported: not those of a
    * first attempt that Silicon retries (see [[viper.silicon.rules.executionFlowController]]).
    */
  def failed(s: State, v: Verifier, failure: Failure): Unit = ()
}

/** Thrown by a [[DebugHook]] to end the verification, e.g. because the debug session was stopped. */
class DebugRunAborted(val reason: String) extends RuntimeException(s"The debug run was aborted: $reason")

/**
  * The "reason" of a proof obligation that was opened at a breakpoint rather than at a failure. It lets the
  * debugger's model (see [[ObligationModelBuilder.errorInfo]]) say where the verification is paused.
  */
case class PausedAtStatement(offendingNode: ast.Stmt) extends ExtensionAbstractErrorReason {
  val id = "debugger.paused"
  def readableMessage: String = s"Paused before ${offendingNode.toString().linesIterator.nextOption().getOrElse("")}"
  def withNode(offendingNode: ErrorNode = this.offendingNode): PausedAtStatement =
    PausedAtStatement(offendingNode.asInstanceOf[ast.Stmt])
}
