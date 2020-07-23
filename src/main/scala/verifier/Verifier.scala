// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import java.nio.file.Path

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silicon.{Config, Map}
import viper.silicon.decider.Decider
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.{IdentifierFactory, SymbolConverter}
import viper.silicon.state.terms.{AxiomRewriter, TriggerGenerator}
import viper.silicon.supporters.{PredicateData, QuantifierSupporter, SnapshotSupporter}
import viper.silicon.supporters.functions.FunctionData
import viper.silicon.utils.Counter
import viper.silver.plugin.PluginAwareReporter
import viper.silver.ast.LabelledOld

trait Verifier {
  def uniqueId: String

  def logger: Logger
  def reporter: PluginAwareReporter
  def counter(id: AnyRef): Counter

  def decider: Decider
  def symbolConverter: SymbolConverter
  def stateFormatter: StateFormatter
  def identifierFactory: IdentifierFactory
  def triggerGenerator: TriggerGenerator
  def axiomRewriter: AxiomRewriter
  def quantifierSupporter: QuantifierSupporter
  def snapshotSupporter: SnapshotSupporter

  def verificationPoolManager: VerificationPoolManager
}

/* TODO: Replace getters and setters by public vars
   TODO: Add a description to each var that explain when it is expected to be set */
object Verifier {
  val PRE_STATE_LABEL = "old"
  val MAGIC_WAND_LHS_STATE_LABEL = LabelledOld.LhsOldLabel

  private var _config: Config = _
  def config: Config = _config
  /*private*/ def config_=(config: Config): Unit = { _config = config }

  private var _program: ast.Program = _
  def program: ast.Program = _program
  /*private*/ def program_=(program: ast.Program): Unit = { _program = program }

  private var _inputFile: Option[Path] = None
  def inputFile: Option[Path] = _inputFile
  /*private*/ def inputFile_=(file: Option[Path]): Unit = { _inputFile = file }

  private var _predicateData: Map[ast.Predicate, PredicateData] = _
  def predicateData: Map[ast.Predicate, PredicateData] = _predicateData
  /*private*/ def predicateData_=(predicateData: Map[ast.Predicate, PredicateData]): Unit =
    { _predicateData = predicateData }

  private var _functionData: Map[ast.Function, FunctionData] = _
  def functionData: Map[ast.Function, FunctionData] = _functionData
  /*private*/ def functionData_=(functionData: Map[ast.Function, FunctionData]): Unit =
  { _functionData = functionData }
}

trait VerifierComponent { this: Verifier => }
