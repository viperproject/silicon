// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

/**
  * Renders an [[ObligationModel]] as text. This reproduces exactly what the debugger's CLI printed before the
  * model was introduced; the same model is also sent to IDEs in structured form.
  */
object DebugRenderer {

  def renderObligation(m: ObligationModel): String =
    "\n" +
      renderErrorInfo(m.originalError) +
      renderSection("Branch Conditions", m.branchConditions) +
      renderSection("Store", m.store) +
      m.heaps.map(h => renderSection(h.title, h.chunks)).mkString +
      renderAxioms(m.axioms) +
      renderDeclarations(m.declarations) +
      renderAssumptions(m.assumptions) +
      renderAssertion(m.assertion)

  def renderErrorInfo(e: ErrorInfoModel): String =
    "Original Error: " +
      s"\n\t\t${e.posString}" +
      e.memberName.map(n => s" (inside $n)").getOrElse("") +
      s"\n\t\t${e.message}\n\n"

  /** A flat section, whose entries are printed one per line: branch conditions, the store, a heap. */
  private def renderSection(title: String, nodes: Seq[DebugNode]): String =
    s"$title:\n\t\t${nodes.map(_.label).mkString("\n\t\t")}\n\n"

  private def renderAxioms(axioms: Seq[DebugNode]): String =
    if (axioms.isEmpty) ""
    else s"Axioms: ${axioms.zipWithIndex.map { case (a, i) =>
      s"\n\t[A$i] ${a.label}:\n\t\t${a.children.map(_.label).mkString("\n\t\t")}\n"
    }.mkString}\n\n"

  private def renderDeclarations(decls: Seq[DebugNode]): String =
    if (decls.isEmpty) "" else s"Declarations: ${decls.map(d => s"\n\t${d.label}").mkString}\n\n"

  private def renderAssumptions(assumptions: Seq[DebugNode]): String =
    if (assumptions.isEmpty) "" else s"Assumptions: ${renderNodes(assumptions, 0)}\n\n"

  private def renderAssertion(assertion: DebugNode): String =
    if (assertion.kind == DebugNodeKind.Literal) assertion.label
    else s"Assertion:\n\t${renderNode(assertion, 0)}\n\n"

  def renderNodes(nodes: Seq[DebugNode], depth: Int, showIds: Boolean = true): String =
    nodes.map(renderNode(_, depth, showIds)).mkString

  def renderNode(n: DebugNode, depth: Int, showIds: Boolean = true): String =
    if (n.kind == DebugNodeKind.Literal) n.label
    else {
      // Only assumptions have ids the user can refer to; for other nodes they would just be noise.
      val id = if (showIds) "[" + n.id + "] " else ""
      "\n\t" + ("\t" * depth) + id + n.label + n.childSeparator + renderChildren(n, depth, showIds)
    }

  private def renderChildren(n: DebugNode, depth: Int, showIds: Boolean): String = {
    if (n.childCount == 0) ""
    else if (n.childrenElided) "[...]"
    else {
      val truncated = if (n.children.size < n.childCount) "\n\t" + ("\t" * (depth + 1)) + "[...]" else ""
      renderNodes(n.children, depth + 1, showIds) + truncated
    }
  }

  /** The counterexample as a tree, for clients that prefer it over Silicon's own textual rendering. */
  def renderCounterexample(ce: CounterexampleModel): String = {
    val staleNote = if (ce.stale) "(possibly out of date, the assumptions have changed since)\n" else ""
    if (ce.sections.isEmpty) staleNote + ce.renderedText
    else staleNote + ce.sections.map(s => s"${s.title}:${renderNodes(s.nodes, 0, showIds = false)}\n").mkString("\n")
  }

  def renderFailureList(failures: Seq[DebugFailureInfo]): String =
    failures.map(f => s"[${f.index}]: ${f.message} (${f.posString})\n").mkString("\n")

  def renderMessages(messages: Seq[DebugMessage]): String =
    messages.map(_.text).mkString("\n")

  def renderResult(r: DebugCommandResult): String = renderMessages(r.messages)
}
