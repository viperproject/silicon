// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.Mark
import viper.silicon.state.terms.Term
import viper.silver.ast
import viper.silver.ast.Exp

import scala.annotation.unused
import scala.collection.convert.ImplicitConversions.`map AsJavaMap`

object DebugExp {
  private var idCounter: Int = 0

  def createInstance(description: Option[String],
                     originalExp: Option[ast.Exp],
                     substitutedExp: Option[ast.Exp],
                     terms: InsertionOrderedSet[Term],
                     isInternal_ : Boolean,
                     children: InsertionOrderedSet[DebugExp]
                    ): DebugExp = {
    val debugExp = new DebugExp(idCounter, description, originalExp, substitutedExp, terms, isInternal_, children)
    idCounter += 1
    debugExp
  }

  def createInstance(description: Option[String], originalExp: Option[ast.Exp], substitutedExp: Option[ast.Exp],
                     children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(description, originalExp, substitutedExp, InsertionOrderedSet.empty, false, children)
  }

  def createInstance(description: String, children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(Some(description), None, None, children)
  }

  def createInstance(description: String): DebugExp = {
    createInstance(Some(description), None, None, InsertionOrderedSet.empty)
  }

  def createInstance(description: String, isInternal_ : Boolean): DebugExp = {
    createInstance(Some(description), None, None, InsertionOrderedSet.empty, isInternal_, InsertionOrderedSet.empty)
  }

  def createInstance(originalExp: ast.Exp, substitutedExp: ast.Exp): DebugExp = {
    createInstance(None, Some(originalExp), Some(substitutedExp), InsertionOrderedSet.empty)
  }

  def createImplicationInstance(description: Option[String],
                                originalExp: Option[ast.Exp],
                                substitutedExp: Option[ast.Exp],
                                terms: InsertionOrderedSet[Term],
                                isInternal_ : Boolean,
                                children: InsertionOrderedSet[DebugExp]
                               ): ImplicationDebugExp = {
    val debugExp = new ImplicationDebugExp(idCounter, description, originalExp, substitutedExp, terms, isInternal_, children)
    idCounter += 1
    debugExp
  }

  def createQuantifiedInstance(description: Option[String],
                               originalExp: Option[ast.Exp],
                               substitutedExp: Option[ast.Exp],
                               terms: InsertionOrderedSet[Term],
                               isInternal_ : Boolean,
                               children: InsertionOrderedSet[DebugExp],
                               quantifier: String,
                               qvars: Seq[ast.Exp],
                               triggers: Seq[ast.Trigger]
                              ): QuantifiedDebugExp ={
    val debugExp = new QuantifiedDebugExp(idCounter, description, originalExp, substitutedExp, terms, isInternal_, children, quantifier, qvars, triggers)
    idCounter += 1
    debugExp
  }
}
class DebugExp(val id: Int,
               val description : Option[String],
               val originalExp : Option[ast.Exp],
               val formattedExp : Option[ast.Exp],
               val terms : InsertionOrderedSet[Term],
               val isInternal_ : Boolean,
               val children : InsertionOrderedSet[DebugExp]) {

  def withTerms(newTerms : InsertionOrderedSet[Term]): DebugExp = {
    new DebugExp(id, description, originalExp, formattedExp, newTerms, isInternal_, children)
  }

  def getTerms: InsertionOrderedSet[Term] ={
    if(terms.isEmpty){
      children.flatMap(_.getTerms)
    }else{
      terms
    }
  }

  def isInternal: Boolean = isInternal_

  def removeChildrenById(ids: Seq[Int]): DebugExp ={
    val newChildren = children.filter(i => !ids.contains(i.id)).map(c => c.removeChildrenById(ids))
    new DebugExp(id, description, originalExp, formattedExp, terms, isInternal_, newChildren)
  }

  @unused
  def termsToString: String = {
    terms.map(t => t.toString.replaceAll("@.. ", " ")).mkString(" && ")
  }

  override def toString: String = {
    toString(5, new DebugExpPrintConfiguration)
  }

  def childrenToString(printChildrenDepth: Int, config: DebugExpPrintConfiguration): String = {
    val nonInternalChildren = children.filter(de => config.isPrintInternalEnabled || !de.isInternal)
    if (nonInternalChildren.isEmpty) ""
    else if(printChildrenDepth <= 0) ": [...]"
    else {
      ": (" + nonInternalChildren.tail.foldLeft[String](nonInternalChildren.head.toString(printChildrenDepth-1, config))((s, de) => s + " && " + de.toString(printChildrenDepth-1, config)) + ")"
    }
  }

  def getTopLevelString: String = {
    if (description.isDefined) {
      "[" + id + "] " + description.get + (if (formattedExp.isDefined) " (" + formattedExp.get.toString() + ")" else "")
    } else {
      "[" + id + "] " + formattedExp.get.toString()
    }
  }


  def toString(printChildrenDepth: Int, config: DebugExpPrintConfiguration): String = {
    if(isInternal_ && !config.isPrintInternalEnabled){
      return ""
    }
    getTopLevelString + childrenToString(math.max(printChildrenDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
  }

  def toString(config: DebugExpPrintConfiguration): String = {
    toString(config.printHierarchyLevel, config)
  }

}


class ImplicationDebugExp(id: Int,
                          description : Option[String],
                          originalExp : Option[ast.Exp],
                          formattedExp : Option[ast.Exp],
                          terms : InsertionOrderedSet[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp]) extends DebugExp(id, description, originalExp, formattedExp, terms, isInternal_, children) {

  override def getTerms: InsertionOrderedSet[Term] = terms

  override def childrenToString(printChildrenDepth: Int, config: DebugExpPrintConfiguration): String = {
    val nonInternalChildren = children.filter(de => config.isPrintInternalEnabled || !de.isInternal)
    if (nonInternalChildren.isEmpty) ""
    else if (printChildrenDepth <= 0) " [...]"
    else {
      " (" + nonInternalChildren.tail.foldLeft[String](nonInternalChildren.head.toString(printChildrenDepth - 1, config))((s, de) => s + " && " + de.toString(printChildrenDepth - 1, config)) + ")"
    }
  }

  override def toString(printChildrenDepth: Int, config: DebugExpPrintConfiguration): String = {
      if (isInternal_ && !config.isPrintInternalEnabled) {
        return ""
      }

      if (children.nonEmpty) {
        "(" + getTopLevelString + " ==> " + childrenToString(math.max(1, math.max(printChildrenDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0))), config) + ")"
      }else{
        getTopLevelString
      }
  }
}


class QuantifiedDebugExp(id: Int,
                         description : Option[String],
                         originalExp : Option[ast.Exp],
                         formattedExp : Option[ast.Exp],
                         terms : InsertionOrderedSet[Term],
                         isInternal_ : Boolean,
                         children : InsertionOrderedSet[DebugExp],
                         val quantifier: String,
                         val qvars : Seq[ast.Exp],
                         val triggers: Seq[ast.Trigger]) extends DebugExp(id, description, originalExp, formattedExp, terms, isInternal_, children) {

  override def getTerms: InsertionOrderedSet[Term] = terms

  override def toString(printChildrenDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal_ && !config.isPrintInternalEnabled) {
      return ""
    }

    if (qvars.nonEmpty) {
      "([" + id + "] " + quantifier + " " + qvars.mkString(", ") + " :: (" + childrenToString(math.max(1, math.max(printChildrenDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0))), config) + "))"
    }else{
      getTopLevelString
    }
  }
}


class DebugExpPrintConfiguration {
  var isPrintInternalEnabled: Boolean = true
  var printHierarchyLevel: Int = 100
  var nodeToHierarchyLevelMap: Map[Int, Int] = Map.empty
  var isPrintAxiomsEnabled: Boolean = false

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
    if(strSplit.size < 2){
      println("invalid input")
      return
    }
    val level = strSplit(1).trim.toIntOption
    if(level.isEmpty){
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
      s"printHierarchyLevel    = $printHierarchyLevel\n" +
      s"hierarchy per id  = $nodeToHierarchyLevelMap\n" +
      s"isPrintAxiomsEnabled = $isPrintAxiomsEnabled\n"
  }
}

class DebugAxiom(val description: String, val terms: InsertionOrderedSet[Term]){

  override def toString(): String = {
    s"$description: $terms\n"
  }
}