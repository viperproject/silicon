// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.ErrorReason

/**
  * All state of a single proof obligation the debugger is working on: the symbolic state and verifier at the
  * point of failure, everything needed to re-create a prover for it, the path conditions in both term and
  * expression form, and the assertion that failed.
  *
  * The textual representation is produced by [[DebugRenderer]] from the model built by
  * [[ObligationModelBuilder]], so that CLI output and the structured data sent to an IDE cannot drift apart.
  */
case class ProofObligation(s: State,
                           v: Verifier,
                           proverEmits: Seq[String],
                           preambleAssumptions: Seq[DebugAxiom],
                           branchConditions: Seq[Term],
                           branchConditionExps: Seq[(ast.Exp, ast.Exp)],
                           assumptionsExp: InsertionOrderedSet[DebugExp],
                           assertion: Term,
                           eAssertion: DebugExp,
                           timeout: Option[Int],
                           printConfig: DebugExpPrintConfiguration,
                           originalErrorReason: ErrorReason,
                           /** Absent unless the program was parsed from Viper source; see [[SiliconDebugSession]]. */
                           resolver: Option[DebugResolver],
                           translator: Option[DebugTranslator]
                          ){

  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    val newAssumptionsExp = assumptionsExp.filter(a => !ids.contains(a.id)).map(c => c.removeChildrenById(ids))
    this.copy(assumptionsExp = newAssumptionsExp)
  }

  def toModel(failureIndex: Int = 0): ObligationModel =
    ObligationModelBuilder.build(this, failureIndex)

  override def toString: String = DebugRenderer.renderObligation(toModel())
}
