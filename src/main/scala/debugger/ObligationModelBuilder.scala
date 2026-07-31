// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.terms.True
import viper.silicon.state.{BasicChunk, Heap, MagicWandChunk, QuantifiedFieldChunk, QuantifiedMagicWandChunk, QuantifiedPredicateChunk}
import viper.silver.ast
import viper.silver.ast.utility.Simplifier

/**
  * Turns a [[ProofObligation]] into an [[ObligationModel]]. The labels produced here are exactly the strings
  * the debugger's CLI used to print, so that [[DebugRenderer]] can reassemble the original output.
  */
object ObligationModelBuilder {

  /** Synthetic ids for nodes that do not correspond to a `DebugExp`. They are negative so that they cannot
    * collide with `DebugExp` ids (which the user refers to when zooming in on or removing assumptions). */
  private def syntheticId(section: Int, index: Int): Int = -(section * 100000 + index + 1)

  private val StoreSection = 1
  private val HeapSection = 2
  private val BranchSection = 3
  private val AxiomSection = 4
  private val DeclSection = 5

  def build(obl: ProofObligation, failureIndex: Int = 0, proverArgs: Option[String] = None): ObligationModel = {
    val filter = DebugNodeFilter.fromPrintConfig(obl.printConfig)
    ObligationModel(
      failureIndex = failureIndex,
      originalError = errorInfo(obl),
      branchConditions = branchConditionNodes(obl),
      store = storeNodes(obl),
      heaps = heapModels(obl),
      axioms = if (obl.printConfig.isPrintAxiomsEnabled) axiomNodes(obl) else Seq.empty,
      declarations = if (obl.printConfig.isPrintAxiomsEnabled) declarationNodes(obl) else Seq.empty,
      assumptions = assumptionNodes(obl, filter),
      assertion = assertionNode(obl),
      proverName = proverName(obl),
      proverArgs = proverArgs,
      timeoutMs = obl.timeout,
      printConfig = obl.printConfig.toModel)
  }

  private def proverName(obl: ProofObligation): String =
    try obl.v.decider.prover.name catch { case _: Throwable => "" }

  def errorInfo(obl: ProofObligation): ErrorInfoModel =
    ErrorInfoModel(
      message = obl.originalErrorReason.readableMessage,
      posString = obl.originalErrorReason.pos.toString,
      pos = DebugSourcePos.from(obl.originalErrorReason.pos),
      memberName = obl.s.currentMember.map(_.name))

  private def storeNodes(obl: ProofObligation): Seq[DebugNode] = {
    val printTerms = obl.printConfig.printInternalTermRepresentation
    obl.s.g.values.toSeq.zipWithIndex.map { case ((variable, (term, exp)), idx) =>
      val value = if (printTerms) term.toString else exp.map(_.toString).getOrElse(term.toString)
      DebugNode(syntheticId(StoreSection, idx), DebugNodeKind.StoreEntry, s"$variable -> $value",
        expString = exp.map(_.toString), termString = Some(term.toString),
        pos = DebugSourcePos.from(variable))
    }
  }

  private def heapModels(obl: ProofObligation): Seq[DebugHeapModel] = {
    var counter = 0
    def chunkNodes(h: Heap): Seq[DebugNode] = h.values.toSeq.map { c =>
      counter += 1
      DebugNode(syntheticId(HeapSection, counter), DebugNodeKind.Chunk, chunkString(c, obl),
        termString = Some(c.toString))
    }

    if (obl.printConfig.printOldHeaps)
      DebugHeapModel("Current Heap", "current", chunkNodes(obl.s.h)) +:
        obl.s.oldHeaps.toSeq.map { case (k, v) => DebugHeapModel(s"Heap $k", k, chunkNodes(v)) }
    else
      Seq(DebugHeapModel("Heap", "current", chunkNodes(obl.s.h)))
  }

  private def branchConditionNodes(obl: ProofObligation): Seq[DebugNode] = {
    val labels =
      if (obl.printConfig.printInternalTermRepresentation)
        obl.branchConditions.filter(bc => bc != True).map(_.toString)
      else
        obl.branchConditionExps.map(bc => Simplifier.simplify(bc._2, true))
          .filter(bc => bc != ast.TrueLit()()).map(_.toString)
    labels.zipWithIndex.map { case (l, idx) =>
      DebugNode(syntheticId(BranchSection, idx), DebugNodeKind.BranchCondition, l)
    }
  }

  private def axiomNodes(obl: ProofObligation): Seq[DebugNode] =
    obl.preambleAssumptions.zipWithIndex.map { case (a, idx) =>
      val terms = a.terms.toSeq.zipWithIndex.map { case (t, tIdx) =>
        DebugNode(syntheticId(AxiomSection, idx * 1000 + tIdx + 1), DebugNodeKind.Term, t.toString)
      }
      DebugNode(syntheticId(AxiomSection, idx), DebugNodeKind.Axiom, a.description,
        childCount = terms.size, children = terms)
    }

  private def declarationNodes(obl: ProofObligation): Seq[DebugNode] =
    obl.proverEmits.zipWithIndex.map { case (d, idx) =>
      DebugNode(syntheticId(DeclSection, idx), DebugNodeKind.Declaration, d)
    }

  private def assumptionNodes(obl: ProofObligation, filter: DebugNodeFilter): Seq[DebugNode] =
    obl.assumptionsExp.toSeq
      .filter(d => !d.isInternal || filter.includeInternal)
      .flatMap(_.toNode(filter))

  private def assertionNode(obl: ProofObligation): DebugNode = {
    if (obl.eAssertion.finalExp.isDefined) {
      obl.eAssertion.toNode(DebugNodeFilter.assertion)
        .map(_.copy(kind = DebugNodeKind.Assertion))
        .getOrElse(DebugNode(obl.eAssertion.id, DebugNodeKind.Literal, ""))
    } else {
      // The old implementation printed only the description in this case, without any decoration.
      DebugNode(obl.eAssertion.id, DebugNodeKind.Literal, obl.eAssertion.description.getOrElse(""))
    }
  }

  /** Renders a single heap chunk the way the debugger has always rendered it. */
  private def chunkString(c: Chunk, obl: ProofObligation): String = {
    if (obl.printConfig.printInternalTermRepresentation)
      return c.toString
    val s = obl.s
    val res = c match {
      case bc: BasicChunk =>
        val snapExpString = bc.snapExp match {
          case Some(e) => s" -> ${Simplifier.simplify(e, true)}"
          case _ => ""
        }
        bc.resourceID match {
          case FieldID => s"acc(${bc.argsExp.get.head}.${bc.id}, ${Simplifier.simplify(bc.permExp.get, true)})$snapExpString"
          case PredicateID => s"acc(${bc.id}(${bc.argsExp.mkString(", ")}), ${Simplifier.simplify(bc.permExp.get, true)})"
        }
      case mwc: MagicWandChunk =>
        val shape = mwc.id.ghostFreeWand
        val expBindings = mwc.bindings.map(b => b._1 -> b._2._2.get)
        val instantiated = shape.replace(expBindings)
        s"acc(${instantiated.toString}, ${Simplifier.simplify(mwc.permExp.get, true)})"
      case qfc: QuantifiedFieldChunk =>
        if (qfc.singletonRcvrExp.isDefined) {
          val receiver = Simplifier.simplify(qfc.singletonRcvrExp.get, true)
          val perm = Simplifier.simplify(qfc.permExp.get.replace(qfc.quantifiedVarExps.get.head.localVar, receiver), true)
          s"acc(${receiver}.${qfc.id}, ${perm})"
        } else {
          val varsString = qfc.quantifiedVarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val qvarsString = "forall " + qfc.invs.get.qvarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val varsEqualString = qfc.quantifiedVarExps.get.zip(qfc.invs.get.invertibleExps.get).map(v => s"${v._1.name} == ${Simplifier.simplify(v._2, true)}").mkString(" && ")
          s"forall ${varsString} :: ${qvarsString} :: ${varsEqualString} ==> acc(${qfc.quantifiedVarExps.get.head.name}.${qfc.id}, ${Simplifier.simplify(qfc.permExp.get, true)})"
        }
      case qpc: QuantifiedPredicateChunk =>
        if (qpc.singletonArgExps.isDefined) {
          s"acc(${qpc.id}(${qpc.singletonArgExps.get.map(e => Simplifier.simplify(e, true)).mkString(", ")}), ${Simplifier.simplify(qpc.permExp.get, true)})"
        } else {
          val varsString = qpc.quantifiedVarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val qvarsString = "forall " + qpc.invs.get.qvarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val varsEqualString = qpc.quantifiedVarExps.get.zip(qpc.invs.get.invertibleExps.get).map(v => s"${v._1.name} == ${Simplifier.simplify(v._2, true)}").mkString(" && ")
          s"forall ${varsString} :: ${qvarsString} :: ${varsEqualString} ==> acc(${qpc.id}(${qpc.quantifiedVarExps.get.map(_.name).mkString(", ")}), ${Simplifier.simplify(qpc.permExp.get, true)})"
        }
      case qwc: QuantifiedMagicWandChunk =>
        val shape = qwc.id.ghostFreeWand
        if (qwc.singletonArgExps.isDefined) {
          val instantiated = shape.replace(shape.subexpressionsToEvaluate(s.program).zip(qwc.singletonArgExps.get).map(e => e._1 -> Simplifier.simplify(e._2, true)).toMap)
          val permReplaced = Simplifier.simplify(qwc.permExp.get.replace(qwc.quantifiedVarExps.get.zip(qwc.singletonArgExps.get).map(e => e._1.localVar -> e._2).toMap), true)

          s"acc(${instantiated.toString}, ${permReplaced})"
        } else{
          val varsString = qwc.quantifiedVarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val qvarsString = "forall " + qwc.invs.get.qvarExps.get.map(v => s"${v.name}: ${v.typ}").mkString(", ")
          val varsEqualString = qwc.quantifiedVarExps.get.zip(qwc.invs.get.invertibleExps.get).map(v => s"${v._1.name} == ${Simplifier.simplify(v._2, true)}").mkString(" && ")
          val instantiated = shape.replace(shape.subexpressionsToEvaluate(s.program).zip(qwc.invs.get.invertibleExps.get).map(e => e._1 -> Simplifier.simplify(e._2, true)).toMap)
          s"forall ${varsString} :: ${qvarsString} :: ${varsEqualString} ==> acc(${instantiated}, ${Simplifier.simplify(qwc.permExp.get, true)})"
        }
      case other => other.toString
    }
    res
  }
}
