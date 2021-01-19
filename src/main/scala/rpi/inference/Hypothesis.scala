package rpi.inference

import rpi.util.Expressions._
import viper.silver.ast

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
    * Optionally returns the predicaate with the given name.
    *
    * @param name The name of the predicate.
    * @return The predicate.
    */
  @inline
  def getPredicate(name: String): Option[ast.Predicate] =
    predicateMap.get(name)

  /**
    * Returns the predicate corresponding to the given specification.
    *
    * @param specification The specification.
    * @return The predicate.
    */
  def getPredicate(specification: Specification): ast.Predicate =
    getPredicate(specification.name) match {
      case Some(existing) => existing
      case None =>
        val name = specification.name
        val parameters = specification.parameters
        val body = Some(top)
        ast.Predicate(name, parameters, body)()
    }

  /**
    * Returns the body of given predicate instance.
    *
    * @param instance The instance.
    * @return The body.
    */
  def getPredicateBody(instance: Instance): ast.Exp = {
    val body = getPredicate(instance.name)
      .flatMap { predicate => predicate.body }
      .getOrElse(top)
    instance.toActual(body)
  }
}