// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package rpi.inference

import rpi.inference.context.Instance
import rpi.util.ast.Expressions._
import rpi.util.ast.ValueInfo
import viper.silver.ast

object Hypothesis {
  /**
    * The empty hypothesis.
    */
  val empty: Hypothesis =
    Hypothesis(Seq.empty, Seq.empty)

  /**
    * Returns a hypothesis with the given predicates.
    *
    * @param predicates The predicates.
    * @return The hypothesis.
    */
  def apply(predicates: Seq[ast.Predicate]): Hypothesis =
    Hypothesis(Seq.empty, predicates)
}

/**
  * A hypothesis.
  */
case class Hypothesis(lemmas: Seq[ast.Method], predicates: Seq[ast.Predicate]) {
  /**
    * The map from names to lemma methods.
    */
  private lazy val lemmaMap: Map[String, ast.Method] =
    lemmas
      .map { lemma => lemma.name -> lemma }
      .toMap

  /**
    * The map from names to predicates.
    */
  private lazy val predicateMap: Map[String, ast.Predicate] =
    predicates
      .map { predicate => predicate.name -> predicate }
      .toMap

  /**
    * Optionally returns the lemma method with the given name.
    *
    * @param name The name of the lemma.
    * @return The lemma method.
    */
  @inline
  def getLemma(name: String): Option[ast.Method] =
    lemmaMap.get(name)

  /**
    * Returns a method call corresponding to an application of the given lemma instance.
    *
    * @param instance The instance of the lemma.
    * @return The lemma application.
    */
  def getLemmaApplication(instance: Instance): ast.MethodCall =
    getLemma(instance.name) match {
      case Some(lemma) =>
        val arguments = instance.arguments
        val info = ValueInfo(instance)
        makeCall(lemma, arguments, info)
      case _ => sys.error(s"Lemma $instance not defined by hypothesis.")
    }

  /**
    * Returns the precondition of the given lemma instance.
    *
    * @param instance The instance of the lemma.
    * @return The precondition.
    */
  def getLemmaPrecondition(instance: Instance): ast.Exp =
    getLemma(instance.name) match {
      case Some(lemma) =>
        val precondition = makeAnd(lemma.pres)
        instance.toActual(precondition)
      case _ => sys.error(s"Lemma $instance not defined by hypothesis.")
    }

  /**
    * Returns the postcondition of the given lemma instance.
    *
    * @param instance The instance of the lemma.
    * @return The postcondition.
    */
  def getLemmaPostcondition(instance: Instance): ast.Exp =
    getLemma(instance.name) match {
      case Some(lemma) =>
        val postcondition = makeAnd(lemma.posts)
        instance.toActual(postcondition)
      case _ => sys.error(s"Lemma $instance not defined by hypothesis.")
    }

  /**
    * Optionally returns the predicate with the given name.
    *
    * @param name The name of the predicate.
    * @return The predicate.
    */
  @inline
  def getPredicate(name: String): Option[ast.Predicate] =
    predicateMap.get(name)

  /**
    * Returns the body of given predicate instance.
    *
    * @param instance The instance.
    * @return The body.
    */
  def getPredicateBody(instance: Instance): ast.Exp = {
    val body = getPredicate(instance.name)
      .flatMap { predicate => predicate.body }
      .getOrElse(makeTrue)
    instance.toActual(body)
  }
}