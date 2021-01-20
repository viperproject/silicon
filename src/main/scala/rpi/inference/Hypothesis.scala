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
    * Returns a method call corresponding to an application of the given lemma instance.
    *
    * @param instance The instance of the lemma.
    * @return The lemma application.
    */
  def getLemmaApplication(instance: Instance): ast.MethodCall =
    getLemma(instance.name) match {
      case Some(lemma) =>
        val arguments = instance.arguments
        makeCall(lemma, arguments)
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
      case Some(predicate) => predicate
      case None =>
        val name = specification.name
        val parameters = specification.parameters
        val body = Some(makeTrue)
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
      .getOrElse(makeTrue)
    instance.toActual(body)
  }
}