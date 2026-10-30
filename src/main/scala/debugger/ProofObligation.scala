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

import scala.collection.mutable

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
                           translator: Option[DebugTranslator],
                           /** Whether the state changed (by a fold or unfold) after `assertion` was evaluated in it, so
                             * that `assertion` may no longer describe the failed check; see
                             * [[SiliconDebugSession.prove]]. */
                           assertionOutdated: Boolean = false
                          ){

  /**
    * Removes the assumptions with the given ids, with everything nested in them, and the instances of removed
    * quantifiers (see [[SiliconDebugSession.instantiate]]), which only hold because of them.
    */
  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    val removed = mutable.Set.empty[Int]
    def removeAll(de: DebugExp): Unit = if (removed.add(de.id)) de.children.foreach(removeAll)
    val visited = mutable.HashSet.empty[DebugExp]
    def visit(de: DebugExp): Unit =
      if (visited.add(de)) { if (ids.contains(de.id)) removeAll(de) else de.children.foreach(visit) }
    assumptionsExp.foreach(visit)

    val instances = assumptionsExp.toSeq.collect { case i: InstantiationDebugExp => i }
    var orphans = instances.filter(i => removed.contains(i.sourceId) && !removed.contains(i.id))
    while (orphans.nonEmpty) {
      orphans.foreach(removeAll)
      orphans = instances.filter(i => removed.contains(i.sourceId) && !removed.contains(i.id))
    }

    val toRemove = removed.toSeq
    val newAssumptionsExp = assumptionsExp.filter(a => !removed.contains(a.id)).map(c => c.removeChildrenById(toRemove))
    this.copy(assumptionsExp = newAssumptionsExp)
  }

  def toModel(failureIndex: Int = 0): ObligationModel =
    ObligationModelBuilder.build(this, failureIndex)

  override def toString: String = DebugRenderer.renderObligation(toModel())
}
