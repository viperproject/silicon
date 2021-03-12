// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference.context

import rpi.inference.{AtomicAbstraction, Hypothesis}
import rpi.util.ast.Expressions._
import rpi.util.ast.ValueInfo
import viper.silver.ast
import viper.silver.ast.Exp

/**
  * An instance of a specification that needs to be inferred.
  */
sealed trait Instance {
  /**
    * The specification corresponding to this instance.
    *
    * @return The corresponding specification.
    */
  def specification: Specification

  /**
    * The arguments with which the parameters of the specification are instantiated.
    *
    * @return The arguments.
    */
  def arguments: Seq[ast.Exp]

  /**
    * Returns the name of the specification.
    *
    * @return The name of the specification.
    */
  def name: String =
    specification.name

  /**
    * The placeholder expression for the inferred part of the specification.
    */
  lazy val placeholder: ast.PredicateAccessPredicate = {
    val info = ValueInfo(this)
    val predicate = makePredicate(name, arguments)
    makeResource(predicate, info)
  }

  /**
    * The existing part of the specification.
    */
  lazy val existing: Seq[ast.Exp] =
    specification.existing.map { expression => toActual(expression) }

  def all: Seq[ast.Exp] =
    placeholder +: existing

  def all(hypothesis: Hypothesis): Seq[ast.Exp] = {
    val inferred = hypothesis.getPredicateBody(this)
    inferred +: existing
  }

  /**
    * Replaces the formal arguments of the given expression with their corresponding actual counterparts.
    *
    * @param expression The expression to translate.
    * @return The expression in therms of the actual arguments.
    */
  def toActual(expression: ast.Exp): ast.Exp

  /**
    * Returns the atomic predicates in terms of the formal arguments.
    *
    * @return The formal atoms.
    */
  def formalAtoms: Seq[ast.Exp] =
    specification.atoms

  /**
    * Returns the atomic predicates in terms of the actual arguments.
    *
    * @return The actual atoms.
    */
  def actualAtoms: Seq[ast.Exp] =
    specification.atoms.map { atom => toActual(atom) }


  /**
    * Replaces the formal arguments of the given location access with their corresponding actual counterparts.
    *
    * @param access The location access to translate.
    * @return The location access in terms of the actual arguments.
    */
  def toActual(access: ast.LocationAccess): ast.LocationAccess =
    access match {
      case ast.FieldAccess(receiver, field) =>
        ast.FieldAccess(toActual(receiver), field)()
      case ast.PredicateAccess(arguments, name) =>
        val updated = arguments.map { argument => toActual(argument) }
        ast.PredicateAccess(updated, name)()
    }

  /**
    * Replaces the formal arguments of the expressions appearing in given abstraction with their corresponding actual
    * counterparts.
    *
    * @param abstraction The abstraction to translate.
    * @return The abstraction in terms of the actual arguments.
    */
  def toActual(abstraction: AtomicAbstraction): AtomicAbstraction = {
    val updated = abstraction
      .values
      .map { case (atom, value) =>
        toActual(atom) -> value
      }
    AtomicAbstraction(updated)
  }

  /**
    * Returns a copy of the instance with the given arguments.
    *
    * @param arguments The arguments.
    * @return The instance.
    */
  def apply(arguments: Seq[ast.Exp]): Instance =
    BindingInstance(specification, arguments)

  override def toString: String =
    s"$name(${arguments.mkString(", ")})"
}

/**
  * An identity instance of a specification.
  *
  * @param specification The specification.
  */
case class IdentityInstance(specification: Specification) extends Instance {
  override def arguments: Seq[ast.LocalVar] =
    specification.variables

  override def toActual(expression: Exp): Exp =
    expression
}

/**
  * An instance binding the parameters of a specifications to some arguments.
  *
  * @param specification The specification.
  * @param arguments     The arguments.
  */
case class BindingInstance(specification: Specification, arguments: Seq[ast.Exp]) extends Instance {
  /**
    * The substitution map for the formal-to-actual translation.
    */
  private lazy val bindings: Map[String, ast.Exp] =
    substitutionMap(specification.parameters, arguments)

  override def toActual(expression: Exp): Exp =
    substitute(expression, bindings)
}
