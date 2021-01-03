// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import viper.silicon.decider.RecordedPathConditions
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.ast.AbstractLocalVar
import viper.silicon.SiliconRunner

/* TODO: Use a proper pretty-printer such as the one we use for Silver AST nodes and Silicon terms */

trait StateFormatter {
  def format(s: State, pcs: RecordedPathConditions): String
  def format(g: Store): String
  def format(h: Heap): String
  def format(oldHeaps: OldHeaps): String
  def format(pcs: RecordedPathConditions): String
}

class DefaultStateFormatter extends StateFormatter {
  def format(s: State, pcs: RecordedPathConditions): String = {
    val gStr = format(s.g)
    val hStr = format(s.h)
    val oldHeapsStr = format(s.oldHeaps)

    val pcsStr =
      if (SiliconRunner.logger.isTraceEnabled())
        /* TODO: It would be better if the choice between whether or not to include path
         *       conditions in the output were made when instantiating the state formatter
         */
        s"${format(pcs)}\n"
      else
        ""

    s"""Store: $gStr,
       |Heap: $hStr,
       |OHs: $oldHeapsStr,
       |PCs: $pcsStr)""".stripMargin
  }

  def format(g: Store): String = g.values.mkString("(", ", ", ")")
  def format(h: Heap): String = h.values.mkString("(", ", ", ")")

  def format(oldHeaps: OldHeaps): String = {
    oldHeaps.map{case (id, h) => s"$id: ${format(h)}"}.mkString("(", ",\n", ")")
  }

  /** Attention: The current implementation hides non-null and combine terms! **/
  def format(pcs: RecordedPathConditions): String = {
    pcs.assumptions.filterNot {
      case    c: BuiltinEquals if c.p0.isInstanceOf[Combine]
           || c.p1.isInstanceOf[Combine]
           => true
      case Not(BuiltinEquals(_, Null())) => true
      case _ => false
    }.mkString("(", ", ", ")")
  }

  //Methods for SymbexLogger
  def toJson(s: State, pcs: Set[Term]): String = {
    val gStr = toJson(s.g)
    val hStr = toJson(s.h)
    val oldStr = s.oldHeaps.get(Verifier.PRE_STATE_LABEL) match {
      case Some(o) => toJson(o)
      case _ => "[]"
    }
    val pcsStr = toJson(pcs)
    s"""{"store":$gStr,"heap":$hStr,"oldHeap":$oldStr,"pcs":$pcsStr}""".stripMargin
  }

  private def toJson(g: Store): String = {
    val values: Map[AbstractLocalVar, Term] = g.values
    if (values.isEmpty) "[]" else values.map((storeChunk:(AbstractLocalVar,Term)) => {
      s"""{"value":"${storeChunk._1.toString()} -> ${storeChunk._2.toString}","type":"${storeChunk._1.typ}"}"""
    }).mkString("[", ",", "]")
  }

  private def toJson(h: Heap): String = {
    val values = h.values
    if (values.isEmpty) "[]" else values.mkString("[\"", "\",\"", "\"]")
  }

  private def toJson(pcs: Set[Term]): String = {
    /* Attention: Hides non-null and combine terms. */
    val filteredPcs = pcs.filterNot {
      case c: BuiltinEquals if c.p0.isInstanceOf[Combine]
        || c.p1.isInstanceOf[Combine] => true
      case Not(BuiltinEquals(_, Null())) => true
      case _ => false
    }
    if (filteredPcs.isEmpty) "[]" else filteredPcs.mkString("[\"", "\",\"", "\"]")
  }
}
