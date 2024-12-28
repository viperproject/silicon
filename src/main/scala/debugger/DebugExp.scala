// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditions
import viper.silicon.state.terms.{And, Exists, Forall, Implies, Quantification, Term, Trigger, Var}
import viper.silver.ast
import viper.silver.ast.utility.Simplifier

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

object DebugExp {
  private var idCounter: AtomicInteger = new AtomicInteger(0)

  def createInstance(description: Option[String],
                     originalExp: Option[ast.Exp],
                     finalExp: Option[ast.Exp],
                     term: Option[Term],
                     isInternal_ : Boolean,
                     children: InsertionOrderedSet[DebugExp]
                    ): DebugExp = {

    val originalExpSimplified = originalExp.map(Simplifier.simplify(_, true))
    val finalExpSimplified = finalExp.map(Simplifier.simplify(_, true))
    val debugExp = new DebugExp(idCounter.getAndIncrement(), description, originalExpSimplified, finalExpSimplified, term, isInternal_, children)
    debugExp
  }

  def createInstance(description: Option[String], originalExp: Option[ast.Exp], finalExp: Option[ast.Exp],
                     children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(description, originalExp, finalExp, None, isInternal_ = false, children)
  }

  def createInstance(description: String, children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(Some(description), None, None, children)
  }

  def createInstance(description: String): DebugExp = {
    createInstance(Some(description), None, None, InsertionOrderedSet.empty)
  }

  def createInstance(description: String, isInternal_ : Boolean): DebugExp = {
    createInstance(Some(description), None, None, None, isInternal_, InsertionOrderedSet.empty)
  }

  def createInstance(description: String, term: Term, isInternal_ : Boolean): DebugExp = {
    createInstance(Some(description), None, None, Some(term), isInternal_, InsertionOrderedSet.empty)
  }

  def createInstance(originalExp: ast.Exp, finalExp: ast.Exp): DebugExp = {
    createInstance(None, Some(originalExp), Some(finalExp), InsertionOrderedSet.empty)
  }

  def createInstance(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugExp = {
    createInstance(None, Some(originalExp.get), Some(finalExp.get), InsertionOrderedSet.empty)
  }

  def createImplicationInstance(description: Option[String],
                                originalExp: Option[ast.Exp],
                                finalExp: Option[ast.Exp],
                                term: Option[Term],
                                isInternal_ : Boolean,
                                children: InsertionOrderedSet[DebugExp]
                               ): ImplicationDebugExp = {
    val debugExp = new ImplicationDebugExp(idCounter.getAndIncrement(), description, originalExp.map(Simplifier.simplify(_, true)), finalExp.map(Simplifier.simplify(_, true)), term, isInternal_, children)
    debugExp
  }

  def createQuantifiedInstance(description: Option[String],
                               isInternal_ : Boolean,
                               children: InsertionOrderedSet[DebugExp],
                               quantifier: String,
                               qvars: Seq[ast.Exp],
                               tQvars: Seq[Var],
                               triggers: Seq[ast.Trigger],
                               tTriggers: Seq[Trigger]
                              ): QuantifiedDebugExp ={
    val debugExp = new QuantifiedDebugExp(idCounter.getAndIncrement(), description, isInternal_, children, quantifier, qvars, tQvars, triggers, tTriggers)
    debugExp
  }
}
class DebugExp(val id: Int,
               val description : Option[String],
               val originalExp : Option[ast.Exp],
               val finalExp : Option[ast.Exp],
               val term : Option[Term],
               val isInternal_ : Boolean,
               val children : InsertionOrderedSet[DebugExp]) {

  lazy val isGlobal: Boolean = {
    val thisGlobal = term match {
      case Some(t) => PathConditions.isGlobal(t)
      case _ => true
    }
    thisGlobal && children.forall(_.isGlobal)
  }

  def withTerm(newTerm: Term): DebugExp = {
    new DebugExp(id, description, originalExp, finalExp, Some(newTerm), isInternal_, children)
  }

  def getAllTerms(visited: mutable.HashSet[DebugExp]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    term.toSeq ++ children.toSeq.flatMap(_.getAllTerms(visited))
  }

  def isInternal: Boolean = isInternal_

  def removeChildrenById(ids: Seq[Int]): DebugExp ={
    val newChildren = children.filter(i => !ids.contains(i.id)).map(c => c.removeChildrenById(ids))
    new DebugExp(id, description, originalExp, finalExp, term, isInternal_, newChildren)
  }

  override def toString: String = {
    toString(0, 6, new DebugExpPrintConfiguration)
  }

  def childrenToString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    val nonInternalChildren = children.filter(de => config.isPrintInternalEnabled || !de.isInternal)
    if (nonInternalChildren.isEmpty) ""
    else if (maxDepth <= currDepth) "[...]"
    else {
      val resBuilder = new mutable.StringBuilder()
      val childrenToShow = if (config.nChildrenToShow > 0) nonInternalChildren.take(config.nChildrenToShow) else nonInternalChildren
      childrenToShow.foreach(de => resBuilder.addAll(de.toString(currDepth+1, maxDepth, config)))
      if (childrenToShow.size < nonInternalChildren.size) resBuilder.addAll("\n\t" + ("\t"*(currDepth + 1)) + "[...]")
      resBuilder.toString()
    }
  }

  def getTopLevelString(currDepth: Int, config: DebugExpPrintConfiguration): String = {
    val toDisplay = if (config.printInternalTermRepresentation) term else finalExp
    val delimiter = if (toDisplay.isDefined && description.isDefined) ": " else ""
    "\n\t" + ("\t"*currDepth) + "[" + id + "] " + description.getOrElse("") + delimiter + toDisplay.getOrElse("")
  }


  def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal_ && !config.isPrintInternalEnabled){
      return ""
    }
    getTopLevelString(currDepth, config) + childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
  }

  def getExpWithId(id: Int, visited: mutable.HashSet[DebugExp]): Option[DebugExp] = {
    if (visited.contains(this))
      return None
    visited.add(this)
    if (this.id == id) {
      return Some(this)
    }
    val toSearch = children.toSeq
    var found: Option[DebugExp] = None
    var i = 0
    while (found.isEmpty && i < toSearch.size) {
      found = toSearch(i).getExpWithId(id, visited)
      i += 1
    }
    found
  }

  def toString(config: DebugExpPrintConfiguration): String = {
    toString(0, config.printHierarchyLevel, config)
  }

}


class ImplicationDebugExp(id: Int,
                          description : Option[String],
                          originalExp : Option[ast.Exp],
                          finalExp : Option[ast.Exp],
                          term : Option[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp]) extends DebugExp(id, description, originalExp, finalExp, term, isInternal_, children) {

  override def getAllTerms(visited: mutable.HashSet[DebugExp]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    assert(term.isDefined)
    Seq(Implies(term.get, And(children.toSeq.flatMap(_.getAllTerms(visited)))))
  }

  override def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
      if (isInternal_ && !config.isPrintInternalEnabled) {
        return ""
      }

      if (children.nonEmpty) {
        getTopLevelString(currDepth, config) + " ==> " + childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
      } else {
        "true"
      }
  }
}


class QuantifiedDebugExp(id: Int,
                         description : Option[String],
                         isInternal_ : Boolean,
                         children : InsertionOrderedSet[DebugExp],
                         val quantifier: String,
                         val qvars : Seq[ast.Exp],
                         val tQvars: Seq[Var],
                         val triggers: Seq[ast.Trigger],
                         val tTriggers: Seq[Trigger]) extends DebugExp(id, description, None, None, None, isInternal_, children) {
  override def getAllTerms(visited: mutable.HashSet[DebugExp]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    val q = if (quantifier == "QA") Forall else Exists
    Seq(Quantification(q, tQvars, And(children.toSeq.flatMap(_.getAllTerms(visited))), tTriggers))
  }

  override def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal_ && !config.isPrintInternalEnabled) {
      return ""
    }

    if (qvars.nonEmpty) {
      "\n\t" + ("\t"*currDepth) + "[" + id + "] " + (if (quantifier == "QA") "forall" else "exists") + " " + qvars.mkString(", ") + " :: " + childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
    } else {
      getTopLevelString(currDepth, config)
    }
  }
}


class DebugExpPrintConfiguration {
  var isPrintInternalEnabled: Boolean = false
  var nChildrenToShow: Int = 5
  var printHierarchyLevel: Int = 2
  var nodeToHierarchyLevelMap: Map[Int, Int] = Map.empty
  var isPrintAxiomsEnabled: Boolean = false
  var printInternalTermRepresentation: Boolean = false

  def setPrintHierarchyLevel(level: String): Unit ={
    printHierarchyLevel = level match {
      case "full" => 100
      case "top" => 0
      case _ => level.toIntOption match {
        case Some(v) => v
        case None    => printHierarchyLevel
      }
    }
  }

  def addHierarchyLevelForId(str: String): Unit ={
    val strSplit = str.split("->")
    if (strSplit.size < 2){
      println("invalid input")
      return
    }
    val level = strSplit(1).trim.toIntOption
    if (level.isEmpty){
      println("invalid input")
      return
    }
    strSplit(0).split(",").foreach(s_id => s_id.trim.toIntOption match {
      case Some(value) => nodeToHierarchyLevelMap += value -> level.get
      case None =>
    })
  }

  override def toString: String = {
    s"isPrintInternalEnabled = $isPrintInternalEnabled\n" +
      s"nChildrenToShow      = $nChildrenToShow\n" +
      s"printHierarchyLevel  = $printHierarchyLevel\n" +
      s"hierarchy per id     = $nodeToHierarchyLevelMap\n" +
      s"isPrintAxiomsEnabled = $isPrintAxiomsEnabled\n"
  }
}

class DebugAxiom(val description: String, val terms: InsertionOrderedSet[Term]){

  override def toString: String = {
    s"$description:\n\t\t${terms.mkString("\n\t\t")}\n"
  }
}