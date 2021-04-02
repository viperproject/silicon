// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.learner.template

import rpi.inference.context.Specification
import viper.silver.ast

/**
  * A template for some specification that needs to be inferred.
  */
sealed trait Template {
  /**
    * Returns the name of the template.
    *
    * @return The name.
    */
  def name: String =
    specification.name

  /**
    * The specification corresponding to this template.
    */
  val specification: Specification

  /**
    * Returns the parameters of the specification.
    *
    * @return The parameters.
    */
  def parameters: Seq[ast.LocalVarDecl] =
    specification.parameters

  /**
    * Returns the atoms of the specification.
    *
    * @return The atoms.
    */
  def atoms: Seq[ast.Exp] =
    specification.atoms
}

/**
  * A template for a specification predicate that needs to be inferred.
  *
  * @param specification The specification corresponding to the template.
  * @param body          The body representing the structure allowed by the template.
  */
case class PredicateTemplate(specification: Specification, body: TemplateExpression) extends Template {
  override def toString: String =
    s"$specification = $body"
}

/**
  * A template for a lemma method.
  *
  * @param specification The specification corresponding to the template.
  * @param precondition  The expression representing the structure of the precondition.
  * @param postcondition The expression representing the structure of the postcondition.
  */
case class LemmaTemplate(specification: Specification, precondition: TemplateExpression, postcondition: TemplateExpression) extends Template {
  override def toString: String =
    s"$specification\n" +
      s"   requires $precondition\n" +
      s"   ensures $postcondition"
}

/**
  * The super trait for all template expressions.
  */
sealed trait TemplateExpression

/**
  * A template expression representing a conjunction of some conjuncts.
  *
  * @param conjuncts The conjuncts.
  */
case class Conjunction(conjuncts: Seq[TemplateExpression]) extends TemplateExpression {
  override def toString: String =
    conjuncts.mkString("(", " * ", ")")
}

/**
  * A template expression wrapping an expression.
  */
case class Wrapped(expression: ast.Exp) extends TemplateExpression {
  override def toString: String =
    expression.toString()
}

/**
  * A template expression representing a guarded expression.
  *
  * @param guardId The id of the guard.
  * @param body    The guarded expression.
  */
case class Guarded(guardId: Int, body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"(phi_$guardId -> $body)"
}

/**
  * A template expression representing a choice for a variable.
  *
  * @param choiceId The id of the choice.
  * @param variable The variable.
  * @param options  The available options.
  * @param body     The template expression for which the choice has to be made.
  */
case class Choice(choiceId: Int, variable: ast.LocalVar, options: Seq[ast.Exp], body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"(choose $variable from {${options.mkString(", ")}} in $body)"
}

/**
  * A truncated template expression.
  *
  * @param condition The truncation condition.
  * @param body      The truncated template expression.
  */
case class Truncation(condition: ast.Exp, body: TemplateExpression) extends TemplateExpression {
  override def toString: String =
    s"($condition -> $body)"
}

