// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.state.Chunk
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
                           assertionOutdated: Boolean = false,
                           /** What the user changed with debugger commands. */
                           userChanges: UserChanges = UserChanges()
                          ){

  /**
    * Removes the assumptions with the given ids, with everything nested in them, and the instances of removed
    * quantifiers (see [[SiliconDebugSession.instantiate]]), which only hold because of them. Assumptions that come
    * from the program are recorded as removed in [[userChanges]].
    */
  def removeAssumptions(ids: Seq[Int]): ProofObligation = {
    val removed = mutable.Set.empty[Int]
    def removeAll(de: DebugExp): Unit = if (removed.add(de.id)) de.children.foreach(removeAll)
    val visited = mutable.HashSet.empty[DebugExp]
    val removedFromProgram = mutable.ListBuffer.empty[DebugExp]
    def visit(de: DebugExp, addedByUser: Boolean): Unit = if (visited.add(de)) {
      val byUser = addedByUser || userChanges.assumptions.contains(de.id)
      if (ids.contains(de.id)) {
        removeAll(de)
        if (!byUser) removedFromProgram += de
      } else de.children.foreach(visit(_, byUser))
    }
    assumptionsExp.foreach(visit(_, addedByUser = false))

    val instances = assumptionsExp.toSeq.collect { case i: InstantiationDebugExp => i }
    var orphans = instances.filter(i => removed.contains(i.sourceId) && !removed.contains(i.id))
    while (orphans.nonEmpty) {
      orphans.foreach(removeAll)
      orphans = instances.filter(i => removed.contains(i.sourceId) && !removed.contains(i.id))
    }

    val toRemove = removed.toSeq
    val newAssumptionsExp = assumptionsExp.filter(a => !removed.contains(a.id)).map(c => c.removeChildrenById(toRemove))
    this.copy(assumptionsExp = newAssumptionsExp, userChanges = userChanges.copy(
      assumptions = userChanges.assumptions.filter(a => !removed.contains(a._1)),
      removedAssumptions = userChanges.removedAssumptions ++ removedFromProgram.map(_ -> UserChanges.removeCommand)))
  }

  /**
    * This obligation without the chunks of the current heap with the given numbers: chunk `n` is the `n`-th chunk of
    * the heap, which [[ObligationModelBuilder]] shows as `hn`. What was known about the chunks' values stays among
    * the assumptions. Checks that inspect permissions, such as `perm(x.f) == none`, may now hold although they do not
    * in the program.
    */
  def removeChunks(numbers: Seq[Int]): ProofObligation = {
    val chunks = s.h.values.toSeq
    val toRemove = numbers.distinct.flatMap(n => chunks.lift(n - 1))
    changedBy(UserChanges.removeCommand, copy(s = s.copy(h = toRemove.foldLeft(s.h)(_ - _))))
  }

  /**
    * `changed`, which is this obligation after the debugger command `command` changed it, with these changes recorded
    * in [[userChanges]]: what `changed` has and this obligation has not was added by the command, and what this
    * obligation has from the program and `changed` has not was removed by it.
    */
  def changedBy(command: String, changed: ProofObligation): ProofObligation = {
    val c = userChanges
    val ids = assumptionsExp.iterator.map(_.id).toSet
    val chunks = s.h.values.toSeq
    val newChunks = changed.s.h.values.toSeq
    val (restored, added) = newChunks.filterNot(chunks.contains).partition(ch => c.removedChunks.exists(_._1 == ch))
    val removedChunks = chunks.filterNot(ch => newChunks.contains(ch) || c.chunks.contains(ch))
    changed.copy(userChanges = c.copy(
      assumptions = c.assumptions ++ changed.assumptionsExp.iterator.map(_.id).filterNot(ids).map(_ -> command),
      chunks = c.chunks.filter(e => newChunks.contains(e._1)) ++ added.map(_ -> command),
      store = c.store ++ changed.s.g.values.keys.filterNot(s.g.values.contains).map(_ -> command),
      branchConditions = c.branchConditions ++
        (branchConditionExps.size until changed.branchConditionExps.size).map(_ -> command),
      removedChunks = c.removedChunks.filterNot(r => restored.contains(r._1)) ++ removedChunks.map(_ -> command)))
  }

  def toModel(failureIndex: Int = 0): ObligationModel =
    ObligationModelBuilder.build(this, failureIndex)

  override def toString: String = DebugRenderer.renderObligation(toModel())
}

/**
  * What the user changed in a proof obligation with debugger commands, so that it can be told apart from what comes
  * from the program. Each change is attributed to the command that made it, e.g. `unfold list(x)`.
  *
  * @param assumptions        the ids of the top-level assumptions the user added; what is nested in them was added, too.
  * @param chunks             the chunks of the current heap the user added, e.g. by unfolding a predicate.
  * @param store              the variables the user added to the store, i.e. witnesses.
  * @param branchConditions   the indices of the branch conditions the user added, by unfolding a predicate with a
  *                           conditional body.
  * @param removedAssumptions the assumptions from the program the user removed.
  * @param removedChunks      the chunks from the program the user removed, e.g. by folding a predicate.
  */
case class UserChanges(assumptions: Map[Int, String] = Map.empty,
                       chunks: Map[Chunk, String] = Map.empty,
                       store: Map[ast.AbstractLocalVar, String] = Map.empty,
                       branchConditions: Map[Int, String] = Map.empty,
                       removedAssumptions: Seq[(DebugExp, String)] = Seq.empty,
                       removedChunks: Seq[(Chunk, String)] = Seq.empty)

object UserChanges {
  /** The command that removes assumptions; see [[ProofObligation.removeAssumptions]]. */
  val removeCommand = "remove"
}
