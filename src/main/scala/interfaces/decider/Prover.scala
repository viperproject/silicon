// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.decider

import viper.silicon.debugger.DebugAxiom
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.common.config.Version
import viper.silver.components.StatefulComponent
import viper.silicon.{Config, Map}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.verifier.Model

sealed abstract class Result
object Sat extends Result
object Unsat extends Result
object Unknown extends Result

/* TODO: Should be generic, not hardcoded to Strings */
trait ProverLike {
  protected val debugMode = Verifier.config.enableDebugging()
  var preambleAssumptions: Seq[DebugAxiom] = Seq()
  def emit(content: String): Unit
  def emit(contents: Iterable[String]): Unit = { contents foreach emit }
  def emitSettings(contents: Iterable[String]): Unit
  def assumeAxioms(terms: InsertionOrderedSet[Term], description: String): Unit = {
    if (debugMode)
      preambleAssumptions :+= new DebugAxiom(description, terms)
    terms foreach assume
  }
  def setOption(name: String, value: String): String
  def assume(term: Term): Unit
  def declare(decl: Decl): Unit
  def comment(content: String): Unit
  def saturate(timeout: Int, comment: String): Unit
  def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit
}

trait Prover extends ProverLike with StatefulComponent {
  def start(userArgsString: Option[String]): Unit
  def assert(goal: Term, timeout: Option[Int] = None): Boolean
  def check(timeout: Option[Int] = None): Result
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function
  def statistics(): Map[String, String]
  def hasModel(): Boolean
  def isModelValid(): Boolean
  def getModel(): Model
  def getReasonUnknown(): String
  def clearLastAssert(): Unit
  def name: String
  def minVersion: Version
  def maxVersion: Option[Version]
  def version(): Version
  def staticPreamble: String
  def randomizeSeedsOptions: Seq[String]

  def pushPopScopeDepth: Int

  def push(n: Int = 1, timeout: Option[Int] = None): Unit

  def pop(n: Int = 1): Unit

  def getAllDecls(): Seq[Decl]

  def getAllEmits(): Seq[String]
}
