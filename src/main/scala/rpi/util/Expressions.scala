package rpi.util

import viper.silver.{ast => sil}

object Expressions {
  /**
    * Instantiates the given predicate with the given arguments.
    *
    * @param predicate The predicate.
    * @param arguments The arguments.
    * @return The instantiated predicate.
    */
  def instantiate(predicate: sil.Predicate, arguments: Seq[sil.Exp]): sil.Exp =
    predicate.body match {
      case Some(body) =>
        val names = predicate.formalArgs.map(_.name)
        val substitutions = names.zip(arguments).toMap
        body.transform {
          case variable@sil.LocalVar(name, _) =>
            substitutions.getOrElse(name, variable)
        }
      case _ => ???
    }

  /**
    * Returns the disjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The disjunction.
    */
  def bigOr(expressions: Iterable[sil.Exp]): sil.Exp =
    expressions
      .reduceOption[sil.Exp](sil.Or(_, _)())
      .getOrElse(sil.FalseLit()())

  /**
    * Returns the conjunction of the given expressions.
    *
    * @param expressions The expressions.
    * @return The conjunction.
    */
  def bigAnd(expressions: Iterable[sil.Exp]): sil.Exp =
    expressions
      .reduceOption[sil.Exp](sil.And(_, _)())
      .getOrElse(sil.TrueLit()())

  /**
    * Returns an expression that is true if exactly on of the given expressions is true.
    *
    * @param expressions The expressions.
    * @return The resulting expression.
    */
  def one(expressions: Iterable[sil.Exp]): sil.Exp = {
    val atLeast = bigOr(expressions)
    val atMost = {
      val pairs = Collections.pairs(expressions)
      bigAnd(pairs.map { case (first, second) => sil.Not(sil.And(first, second)())() })
    }
    sil.And(atLeast, atMost)()
  }

  def simplify(expression: sil.Exp): sil.Exp = expression match {
    case sil.And(sil.TrueLit(), right) => right
    case sil.And(left, sil.TrueLit()) => left
    case sil.Or(sil.FalseLit(), right) => right
    case sil.Or(left, sil.FalseLit()) => left
    case _ => expression
  }
}
