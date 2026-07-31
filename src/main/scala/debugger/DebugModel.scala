// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silver.ast

/**
  * A pure data model of a proof obligation, produced by [[ObligationModelBuilder]] and consumed both by
  * [[DebugRenderer]] (which turns it back into the textual representation used by the CLI) and by clients
  * that want to display it structurally, such as ViperServer's LSP debugger integration.
  *
  * The model deliberately contains no Silicon-internal types, so it can be serialized and sent to an IDE.
  */

/** A source position of a debug node, in 1-based Viper coordinates. */
case class DebugSourcePos(file: String, startLine: Int, startColumn: Int, endLine: Int, endColumn: Int)

object DebugSourcePos {
  def from(pos: ast.Position): Option[DebugSourcePos] = pos match {
    case sp: ast.AbstractSourcePosition =>
      val end = sp.end.getOrElse(sp.start)
      Some(DebugSourcePos(sp.file.toString, sp.start.line, sp.start.column, end.line, end.column))
    case lc: ast.HasLineColumn =>
      Some(DebugSourcePos("", lc.line, lc.column, lc.line, lc.column))
    case _ =>
      None
  }

  def from(n: ast.Node): Option[DebugSourcePos] = n match {
    case p: ast.Positioned => from(p.pos)
    case _ => None
  }
}

object DebugNodeKind {
  /** A node whose label is to be printed verbatim, without id or indentation. */
  val Literal = "literal"
  val Assumption = "assumption"
  val Implication = "implication"
  val Quantified = "quantified"
  val StoreEntry = "store"
  val Chunk = "chunk"
  val BranchCondition = "branchCondition"
  val Axiom = "axiom"
  val Term = "term"
  val Declaration = "declaration"
  val Assertion = "assertion"

  /* Counterexamples */
  val Value = "value"
  val Reference = "reference"
  val Field = "field"
  val Predicate = "predicate"
  val Collection = "collection"
  val Domain = "domain"
  val Function = "function"
  val FunctionCase = "functionCase"
}

/**
  * A node of the proof obligation tree.
  *
  * @param id             the id of the underlying [[DebugExp]], or a negative synthetic id for nodes that do
  *                       not correspond to a `DebugExp` (store entries, heap chunks, axioms, ...).
  * @param label          the text describing this node, without indentation and without the `[id]` prefix.
  * @param childCount     the total number of children after filtering; may exceed `children.size` if the
  *                       children were truncated, in which case a client may request them via `expand`.
  * @param childrenElided true iff the children were dropped because the maximal depth was reached (as
  *                       opposed to being truncated because there were too many of them).
  * @param childSeparator the string printed between this node's label and its children by [[DebugRenderer]].
  */
case class DebugNode(id: Int,
                     kind: String,
                     label: String,
                     description: Option[String] = None,
                     expString: Option[String] = None,
                     termString: Option[String] = None,
                     isInternal: Boolean = false,
                     childCount: Int = 0,
                     childrenElided: Boolean = false,
                     childSeparator: String = "",
                     pos: Option[DebugSourcePos] = None,
                     children: Seq[DebugNode] = Seq.empty) {

  /** True iff a client should offer to expand this node to obtain children it has not received yet. */
  def hasHiddenChildren: Boolean = children.size < childCount
}

/** The chunks of a single heap. `key` is `"current"` or the label of an old heap; `title` is what the CLI prints. */
case class DebugHeapModel(title: String, key: String, chunks: Seq[DebugNode])

case class PrintConfigModel(printInternal: Boolean,
                            nChildrenToShow: Int,
                            hierarchyLevel: Int,
                            printAxioms: Boolean,
                            printInternalTermRepresentation: Boolean,
                            printOldHeaps: Boolean)

case class ErrorInfoModel(message: String,
                          posString: String,
                          pos: Option[DebugSourcePos],
                          memberName: Option[String])

/** A named group of nodes; used for the sections of a counterexample. */
case class DebugSectionModel(title: String, key: String, nodes: Seq[DebugNode])

/**
  * A counterexample: an assignment of values to the variables and heap locations of the current state that
  * satisfies the assumptions but not the assertion, i.e. a concrete situation in which the verification fails.
  *
  * @param sections     the values on return, the values at each labelled (old) state, the domains and the
  *                     functions of the model.
  * @param renderedText the counterexample as Silicon prints it on the command line.
  * @param stale        true if the counterexample was obtained before the current assumptions were last
  *                     changed, i.e. it may no longer be a model of them.
  */
case class CounterexampleModel(sections: Seq[DebugSectionModel],
                               renderedText: String,
                               stale: Boolean = false)

case class ObligationModel(failureIndex: Int,
                           originalError: ErrorInfoModel,
                           branchConditions: Seq[DebugNode],
                           store: Seq[DebugNode],
                           heaps: Seq[DebugHeapModel],
                           axioms: Seq[DebugNode],
                           declarations: Seq[DebugNode],
                           assumptions: Seq[DebugNode],
                           assertion: DebugNode,
                           proverName: String,
                           proverArgs: Option[String],
                           timeoutMs: Option[Int],
                           printConfig: PrintConfigModel,
                           /** A model refuting this obligation, if one has been computed; see [[CounterexampleModel]]. */
                           counterexample: Option[CounterexampleModel] = None)

/** A verification failure that the debugger may be able to open a proof obligation for. */
case class DebugFailureInfo(index: Int,
                            message: String,
                            posString: String,
                            pos: Option[DebugSourcePos],
                            memberName: Option[String],
                            debuggable: Boolean)

object DebugMessageSeverity {
  val Info = "info"
  val Warning = "warning"
  val Error = "error"
}

/** A message the debugger wants to show the user; replaces the `println`s of the old CLI-only implementation. */
case class DebugMessage(severity: String, text: String)

object DebugMessage {
  def info(text: String): DebugMessage = DebugMessage(DebugMessageSeverity.Info, text)
  def warning(text: String): DebugMessage = DebugMessage(DebugMessageSeverity.Warning, text)
  def error(text: String): DebugMessage = DebugMessage(DebugMessageSeverity.Error, text)
}

/**
  * The result of a debugger command.
  *
  * @param obligation the obligation after the command, if there is a current one.
  * @param proved     set only by commands that ran the prover on the proof obligation.
  */
case class DebugCommandResult(ok: Boolean,
                              messages: Seq[DebugMessage],
                              obligation: Option[ObligationModel] = None,
                              proved: Option[Boolean] = None)

object DebugCommandResult {
  def error(text: String): DebugCommandResult = DebugCommandResult(ok = false, Seq(DebugMessage.error(text)))
}

/**
  * Controls how much of the assumption tree [[ObligationModelBuilder]] materializes.
  *
  * The CLI derives this from the user's [[DebugExpPrintConfiguration]] so that the rendered text is exactly
  * what it used to print; an IDE typically requests a shallow tree and expands nodes on demand.
  */
case class DebugNodeFilter(includeInternal: Boolean,
                           maxDepth: Int,
                           maxChildren: Int,
                           perNodeDepth: Map[Int, Int],
                           useTermRepresentation: Boolean) {

  /** The maximal depth to use below the node with the given id. */
  def depthFor(id: Int): Int = math.max(maxDepth, perNodeDepth.getOrElse(id, 0))
}

object DebugNodeFilter {
  def fromPrintConfig(c: DebugExpPrintConfiguration): DebugNodeFilter =
    DebugNodeFilter(c.isPrintInternalEnabled, c.printHierarchyLevel, c.nChildrenToShow,
      c.nodeToHierarchyLevelMap, c.printInternalTermRepresentation)

  /**
    * The filter used for the failed assertion. The old implementation printed it via `DebugExp.toString`,
    * i.e. with a default print configuration and a maximal depth of 6, irrespective of the user's settings.
    */
  val assertion: DebugNodeFilter = fromPrintConfig(new DebugExpPrintConfiguration).copy(maxDepth = 6)
}
