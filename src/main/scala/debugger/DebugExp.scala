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
class DebugExp(val str : Option[String],
               val exp : Option[ast.Exp],
               val substitutedExp : Option[ast.Exp],
               val terms : InsertionOrderedSet[Term],
               val isInternal_ : Boolean,
               val children : InsertionOrderedSet[DebugExp]) {

  def this(str: Option[String], @unused exp: Option[ast.Exp], substitutedExp: Option[ast.Exp],
            children: InsertionOrderedSet[DebugExp]) = {
    this(str, exp, substitutedExp, InsertionOrderedSet.empty, false, children)
  }

  def this(str : String, children : InsertionOrderedSet[DebugExp]) = {
    this(Some(str), None, None, children)
  }

  def this(str : String) = {
    this(Some(str), None, None, InsertionOrderedSet.empty)
  }

  def this(str: String, isInternal_ : Boolean) = {
    this(Some(str), None, None, InsertionOrderedSet.empty, isInternal_, InsertionOrderedSet.empty)
  }

  def this(exp : ast.Exp, substitutedExp : ast.Exp) = {
    this(None, Some(exp), Some(substitutedExp), InsertionOrderedSet.empty)
  }

  def withTerms(newTerms : InsertionOrderedSet[Term]): DebugExp = {
    new DebugExp(str, exp, substitutedExp, newTerms, isInternal_, children)
  }

  def getTerms(): InsertionOrderedSet[Term] ={
    terms
  }

  def isInternal(): Boolean = isInternal_

  @unused
  def termsToString: String = {
    terms.map(t => t.toString.replaceAll("@.. ", " ")).mkString(" && ")
  }

  override def toString: String = {
    toString(printInternals = true, 5)
  }

  def childrenToString(printInternals: Boolean, printChildrenDepth: Int): String = {
    val nonInternalChildren = children.filter(de => printInternals || !de.isInternal())
    if (nonInternalChildren.isEmpty || printChildrenDepth <= 0) ""
    else {
      "(" + nonInternalChildren.tail.foldLeft[String](nonInternalChildren.head.toString(printInternals, printChildrenDepth - 1))((s, de) => s + " && " + de.toString(printInternals, printChildrenDepth - 1)) + ")"
    }
  }

  def getTopLevelString() : String = {
    if (str.isDefined) {
      str.get + (if (substitutedExp.isDefined) " (" + substitutedExp.get.toString() + ")" else "")
    } else {
      substitutedExp.get.toString()
    }
  }


  def toString(printInternals: Boolean, printChildrenDepth: Int): String = {
    if(isInternal_ && !printInternals){
      return ""
    }

    if (children.isEmpty || printChildrenDepth <= 0) getTopLevelString() + ""
    else "(" + getTopLevelString() + ": " + childrenToString(printInternals, printChildrenDepth) + ")"
  }

}


class ImplicationDebugExp(str : Option[String],
                          exp : Option[ast.Exp],
                          substitutedExp : Option[ast.Exp],
                          terms : InsertionOrderedSet[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp]) extends DebugExp(str, exp, substitutedExp, terms, isInternal_, children) {

  override def toString(printInternals: Boolean, printChildrenDepth: Mark): String = {
      if (isInternal_ && !printInternals) {
        return ""
      }

      if (children.nonEmpty) {
        "(" + getTopLevelString() + " ==> (" + childrenToString(printInternals, math.max(printChildrenDepth, 1)) + "))"
      }else{
        getTopLevelString()
      }
  }
}


class QuantifiedDebugExp(str : Option[String],
                          exp : Option[ast.Exp],
                          substitutedExp : Option[ast.Exp],
                          terms : InsertionOrderedSet[Term],
                          isInternal_ : Boolean,
                          children : InsertionOrderedSet[DebugExp],
                          val quantifier: String,
                          val qvars : Seq[ast.Exp]) extends DebugExp(str, exp, substitutedExp, terms, isInternal_, children) {

  override def toString(printInternals: Boolean, printChildrenDepth: Mark): String = {
    if (isInternal_ && !printInternals) {
      return ""
    }

    if (qvars.nonEmpty) {
      "(" + quantifier + " " + qvars.mkString(", ") + " :: (" + childrenToString(printInternals, math.max(printChildrenDepth, 1)) + "))"
    }else{
      getTopLevelString()
    }
  }
}
