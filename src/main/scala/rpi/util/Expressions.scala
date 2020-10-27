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
        substitute(body, substitutions)
      case _ => ???
    }

  /**
    * Substitutes all variables of the given expression according to the given substitutions.
    *
    * @param expression    The expression.
    * @param substitutions The substitutions.
    * @return The substituted expression.
    */
  def substitute(expression: sil.Exp, substitutions: Map[String, sil.Exp]): sil.Exp =
    expression.transform {
      case variable@sil.LocalVar(name, _) =>
        substitutions.getOrElse(name, variable)
    }

  /**
    * TODO: Is this final?
    *
    * @param expression The expression.
    */
  def toSeq(expression: sil.Exp): Seq[String] = expression match {
    case sil.LocalVar(name, _) => Seq(name)
    case sil.FieldAccess(receiver, field) => toSeq(receiver) :+ field.name
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

  /**
    * Simplifies the given expression.
    *
    * @param expression The expression to simplify.
    * @return The simplified expression.
    */
  def simplify(expression: sil.Exp): sil.Exp = expression match {
    case sil.And(left, right) => (left, right) match {
      case (sil.TrueLit(), _) => simplify(right)
      case (_, sil.TrueLit()) => simplify(left)
      case _ => sil.And(simplify(left), simplify(right))()
    }
    case sil.Or(left, right) => (left, right) match {
      case (sil.FalseLit(), _) => simplify(right)
      case (_, sil.FalseLit()) => simplify(left)
      case _ => sil.Or(simplify(left), simplify(right))()
    }
    case _ => expression
  }
}
