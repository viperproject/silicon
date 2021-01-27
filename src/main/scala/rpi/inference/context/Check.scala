package rpi.inference.context

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

  def depth: Int =
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
    // TODO: Take into account specification.
    lazy val depth: Int =
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