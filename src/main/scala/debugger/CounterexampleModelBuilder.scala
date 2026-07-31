// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.interfaces.{SiliconCounterexample, SiliconMappedCounterexample}
import viper.silicon.reporting._
import viper.silver.verifier.Counterexample

/**
  * Turns a counterexample into the same node model the proof obligation uses, so that an IDE can show both in
  * the same way.
  *
  * Only mapped counterexamples (`--counterexample=mapped`) carry enough structure to be shown as a tree; for
  * the other kinds, and for counterexamples of other verifiers, the textual representation is used as-is.
  */
object CounterexampleModelBuilder {

  /** How deep values are expanded. Cyclic references are already cut off by the converter, but domain values
    * carry the functions defined on them, which can nest arbitrarily. */
  private val MaxDepth = 6

  def build(ce: Counterexample, stale: Boolean = false): CounterexampleModel = ce match {
    case mapped: SiliconMappedCounterexample => buildMapped(mapped, stale)
    case other => CounterexampleModel(Seq.empty, safeToString(other), stale)
  }

  def build(ce: SiliconCounterexample): CounterexampleModel = build(ce.asInstanceOf[Counterexample], stale = false)

  private def buildMapped(ce: SiliconMappedCounterexample, stale: Boolean): CounterexampleModel = {
    val counter = new IdCounter
    val converter = ce.converter
    val interpreter = ce.interpreter

    /* Domain values are only readable once the functions defined on them have been applied. */
    def interpret(e: ExtractedModelEntry): ExtractedModelEntry =
      try interpreter.interpret(e, Seq()) catch { case _: Throwable => e }

    def modelSection(title: String, key: String, model: ExtractedModel): DebugSectionModel =
      DebugSectionModel(title, key, model.entries.toSeq.sortBy(_._1).map {
        case (name, entry) => valueNode(counter, name, interpret(entry), 0)
      })

    val onReturn = modelSection("Values", "current", converter.extractedModel)
    val labelled = converter.modelAtLabel.toSeq.sortBy(_._1).map {
      case (label, model) => modelSection(s"Values at $label", label, model)
    }
    val domains =
      if (converter.domains.isEmpty) Seq.empty
      else Seq(DebugSectionModel("Domains", "domains", converter.domains.map(domainNode(counter, _))))
    val functions =
      if (converter.nonDomainFunctions.isEmpty) Seq.empty
      else Seq(DebugSectionModel("Functions", "functions",
        converter.nonDomainFunctions.map(functionNode(counter, _))))

    val sections = (onReturn +: labelled) ++ domains ++ functions
    CounterexampleModel(sections.filter(_.nodes.nonEmpty), safeToString(ce), stale)
  }

  /** The counterexample's own rendering; it does a lot of work and is not guaranteed to succeed. */
  private def safeToString(ce: Counterexample): String =
    try ce.toString catch { case e: Throwable => s"<the counterexample could not be printed: ${e.getMessage}>" }

  // -------------------------------------------------------------------------------------------------------

  /** A single `name -> value` entry, with the structure of the value as its children. */
  private def valueNode(counter: IdCounter, name: String, entry: ExtractedModelEntry, depth: Int): DebugNode = {
    val (kind, value, children) = describe(counter, entry, depth)
    DebugNode(counter.next(), kind, s"$name -> $value",
      termString = Some(entry.toString.linesIterator.mkString(" ")),
      childCount = children.size, children = children)
  }

  /**
    * A short description of a value and, where the value is structured, its parts.
    *
    * @return the kind of the node, the value shown next to the name, and the children.
    */
  private def describe(counter: IdCounter, entry: ExtractedModelEntry, depth: Int): (String, String, Seq[DebugNode]) = {
    if (depth >= MaxDepth) {
      return (DebugNodeKind.Value, oneLine(entry), Seq.empty)
    }
    entry match {
      case RefEntry(name, fields) =>
        val children = fields.toSeq.sortBy(_._1).map { case (field, (value, perm)) =>
          val permString = perm.map(p => s" [${p.toString}]").getOrElse("")
          val (_, valueString, grandChildren) = describe(counter, value, depth + 1)
          DebugNode(counter.next(), DebugNodeKind.Field, s"$field$permString -> $valueString",
            childCount = grandChildren.size, children = grandChildren)
        }
        (DebugNodeKind.Reference, name, children)

      case NullRefEntry(name) => (DebugNodeKind.Reference, s"null ($name)", Seq.empty)
      case RecursiveRefEntry(name) => (DebugNodeKind.Reference, s"$name (recursive)", Seq.empty)

      case SeqEntry(name, values) =>
        (DebugNodeKind.Collection, s"$name, ${values.size} element(s)",
          values.zipWithIndex.map { case (v, i) => valueNode(counter, s"[$i]", v, depth + 1) })

      case SetEntry(name, values) =>
        (DebugNodeKind.Collection, s"$name, ${values.size} element(s)",
          values.toSeq.zipWithIndex.map { case (v, i) => valueNode(counter, s"[$i]", v, depth + 1) })

      case MultiSetEntry(name, values) =>
        (DebugNodeKind.Collection, s"$name, ${values.size} element(s)",
          values.toSeq.map { case (v, n) => valueNode(counter, s"${n}x", v, depth + 1) })

      case PredHeapEntry(name, args, perm) =>
        (DebugNodeKind.Predicate, s"$name(${args.map(oneLine).mkString(", ")})${perm.map(p => s" [$p]").getOrElse("")}",
          Seq.empty)

      case ExtendedDomainValueEntry(original, info) =>
        (DebugNodeKind.Domain, original.toString, info.toSeq.sortBy(_._1.fname).map { case (fn, value) =>
          valueNode(counter, fn.fname, value, depth + 1)
        })

      case other => (DebugNodeKind.Value, oneLine(other), Seq.empty)
    }
  }

  private def domainNode(counter: IdCounter, domain: DomainEntry): DebugNode =
    DebugNode(counter.next(), DebugNodeKind.Domain, domain.valueName,
      childCount = domain.functions.size,
      children = domain.functions.map(functionNode(counter, _)))

  /** A function of the model, with one child per argument tuple it is defined for. */
  private def functionNode(counter: IdCounter, fn: ExtractedFunction): DebugNode = {
    val signature = s"${fn.fname}(${fn.argtypes.mkString(", ")}): ${fn.returnType}"
    val cases = fn.options.toSeq.map { case (args, value) =>
      DebugNode(counter.next(), DebugNodeKind.FunctionCase,
        s"${args.map(oneLine).mkString(", ")} -> ${oneLine(value)}")
    }
    val default = DebugNode(counter.next(), DebugNodeKind.FunctionCase, s"otherwise -> ${oneLine(fn.default)}")
    val children = cases :+ default
    DebugNode(counter.next(), DebugNodeKind.Function, signature, childCount = children.size, children = children)
  }

  private def oneLine(entry: ExtractedModelEntry): String = entry.toString.linesIterator.mkString(" ").trim

  /** Counterexample nodes do not correspond to assumptions, so they get their own negative ids. */
  private class IdCounter {
    private var current = -1000000
    def next(): Int = { current -= 1; current }
  }
}
