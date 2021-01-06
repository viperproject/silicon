package rpi.inference

import viper.silver.ast

/**
  * A hypothesis.
  */
case class Hypothesis(predicates: Map[String, ast.Predicate]) {
  def get(name: String): ast.Exp =
    predicates
      .get(name)
      .flatMap { predicate => predicate.body }
      .getOrElse(ast.TrueLit()())

  def get(instance: Instance): ast.Exp = {
    val body = get(instance.name)
    instance.toActual(body)
  }
}