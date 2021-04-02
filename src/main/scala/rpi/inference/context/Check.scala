// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.context

import rpi.inference.annotation.AccessAnalysis.Depth
import rpi.inference.annotation.AccessAnalysis
import viper.silver.ast

/**
  * A check.
  *
  * @param name The name of the check.
  */
abstract class Check(val name: String) {
  private var self: CheckBody = _

  /**
    * Returns the body of the check.
    *
    * @return The body.
    */
  def body: ast.Seqn =
    self.body

  def depth: Depth =
    self.depth

  /**
    * Sets the body of the check.
    *
    * @param body The body to set.
    */
  def setBody(body: ast.Seqn): Unit =
    self = new CheckBody(body)

  override def toString: String =
    name

  private class CheckBody(val body: ast.Seqn) {
    lazy val depth: Depth =
      AccessAnalysis.accessDepth(body)
  }

}

/**
  * A self-framing check for a specification.
  * TODO: Use or remove.
  *
  * @param name          The name of the check.
  * @param specification The specification.
  */
class FramingCheck(name: String, specification: Specification) extends Check(name)

/**
  * A check corresponding to a method.
  *
  * @param name          The name of the check.
  * @param precondition  The precondition of the method.
  * @param postcondition The postcondition of the method.
  */
class MethodCheck(name: String, val precondition: Instance, val postcondition: Instance) extends Check(name)

/**
  * A check corresponding to a loop.
  *
  * @param name      The name of the check.
  * @param invariant The loop invariant.
  */
class LoopCheck(name: String, val invariant: Instance) extends Check(name)