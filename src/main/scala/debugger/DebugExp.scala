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

import scala.annotation.unused

object DebugExp {
  private var idCounter: Int = 0

  def createInstance(str: Option[String],
                     exp: Option[ast.Exp],
                     substitutedExp: Option[ast.Exp],
                     terms: InsertionOrderedSet[Term],
                     isInternal_ : Boolean, 
                     children: InsertionOrderedSet[DebugExp]
                    ): DebugExp = {
    val debugExp = new DebugExp(idCounter, str, exp, substitutedExp, terms, isInternal_, children)
    idCounter += 1
    debugExp
  }

  def createInstance(str: Option[String], exp: Option[ast.Exp], substitutedExp: Option[ast.Exp],
           children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(str, exp, substitutedExp, InsertionOrderedSet.empty, false, children)
  }

  def createInstance(str: String, children: InsertionOrderedSet[DebugExp]): DebugExp = {
    createInstance(Some(str), None, None, children)
  }

  def createInstance(str: String): DebugExp = {
    createInstance(Some(str), None, None, InsertionOrderedSet.empty)
  }

  def createInstance(str: String, isInternal_ : Boolean): DebugExp = {
    createInstance(Some(str), None, None, InsertionOrderedSet.empty, isInternal_, InsertionOrderedSet.empty)
  }

  def createInstance(exp: ast.Exp, substitutedExp: ast.Exp): DebugExp = {
    createInstance(None, Some(exp), Some(substitutedExp), InsertionOrderedSet.empty)
  }

  def createImplicationInstance(str: Option[String],
                                exp: Option[ast.Exp],
                                substitutedExp: Option[ast.Exp],
                                terms: InsertionOrderedSet[Term],
                                isInternal_ : Boolean,
                                children: InsertionOrderedSet[DebugExp]
                               ): ImplicationDebugExp = {
    val debugExp = new ImplicationDebugExp(idCounter, str, exp, substitutedExp, terms, isInternal_, children)
    idCounter += 1
    debugExp
  }

  def createQuantifiedInstance(str: Option[String],
                               exp: Option[ast.Exp],
                               substitutedExp: Option[ast.Exp],
                               terms: InsertionOrderedSet[Term],
                               isInternal_ : Boolean,
                               children: InsertionOrderedSet[DebugExp],
                               quantifier: String,
                               qvars: Seq[ast.Exp]
                              ): QuantifiedDebugExp ={
    val debugExp = new QuantifiedDebugExp(idCounter, str, exp, substitutedExp, terms, isInternal_, children, quantifier, qvars)
    idCounter += 1
    debugExp
  }
}
class DebugExp(val id: Int,
                val str : Option[String],
               val exp : Option[ast.Exp],
               val substitutedExp : Option[ast.Exp],
               val terms : InsertionOrderedSet[Term],
               val isInternal_ : Boolean,
               val children : InsertionOrderedSet[DebugExp]) {

  def withTerms(newTerms : InsertionOrderedSet[Term]): DebugExp = {
    DebugExp.createInstance(str, exp, substitutedExp, newTerms, isInternal_, children)
  }

  def getTerms: InsertionOrderedSet[Term] ={
    if(terms.isEmpty){
      children.flatMap(_.getTerms)
    }else{
      terms
    }
  }

  def isInternal: Boolean = isInternal_

  @unused
  def termsToString: String = {
    terms.map(t => t.toString.replaceAll("@.. ", " ")).mkString(" && ")
  }

  override def toString: String = {
    toString(printInternals = true, 5)
  }

  def childrenToString(printInternals: Boolean, printChildrenDepth: Int): String = {
    val nonInternalChildren = children.filter(de => printInternals || !de.isInternal)
    if (nonInternalChildren.isEmpty || printChildrenDepth <= 0) ""
    else {
      "(" + nonInternalChildren.tail.foldLeft[String](nonInternalChildren.head.toString(printInternals, printChildrenDepth - 1))((s, de) => s + " && " + de.toString(printInternals, printChildrenDepth - 1)) + ")"
    }
  }

  def getTopLevelString: String = {
    if (str.isDefined) {
      "[" + id + "] " + str.get + (if (substitutedExp.isDefined) " (" + substitutedExp.get.toString() + ")" else "")
    } else {
      "[" + id + "] " + substitutedExp.get.toString()
    }
  }


  def toString(printInternals: Boolean, printChildrenDepth: Int): String = {
    if(isInternal_ && !printInternals){
      return ""
    }

    if (children.isEmpty || printChildrenDepth <= 0) getTopLevelString + ""
    else "(" + getTopLevelString + ": " + childrenToString(printInternals, printChildrenDepth) + ")"
  }

}


class ImplicationDebugExp(id: Int,
                           str : Option[String],
                          exp : Option[ast.Exp],
                          substitutedExp : Option[ast.Exp],
                          terms : InsertionOrderedSet[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp]) extends DebugExp(id, str, exp, substitutedExp, terms, isInternal_, children) {

  override def getTerms: InsertionOrderedSet[Term] = terms

  override def toString(printInternals: Boolean, printChildrenDepth: Mark): String = {
      if (isInternal_ && !printInternals) {
        return ""
      }

      if (children.nonEmpty) {
        "(" + getTopLevelString + " ==> (" + childrenToString(printInternals, math.max(printChildrenDepth, 1)) + "))"
      }else{
        getTopLevelString
      }
  }
}


class QuantifiedDebugExp(id: Int,
                          str : Option[String],
                          exp : Option[ast.Exp],
                          substitutedExp : Option[ast.Exp],
                          terms : InsertionOrderedSet[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp],
                          val quantifier: String,
                          val qvars : Seq[ast.Exp]) extends DebugExp(id, str, exp, substitutedExp, terms, isInternal_, children) {

  override def getTerms: InsertionOrderedSet[Term] = terms

  override def toString(printInternals: Boolean, printChildrenDepth: Mark): String = {
    if (isInternal_ && !printInternals) {
      return ""
    }

    if (qvars.nonEmpty) {
      "([" + id + "] " + quantifier + " " + qvars.mkString(", ") + " :: (" + childrenToString(printInternals, math.max(printChildrenDepth, 1)) + "))"
    }else{
      getTopLevelString
    }
  }
}
