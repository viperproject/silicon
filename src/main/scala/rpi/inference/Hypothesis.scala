package rpi.inference

import viper.silver.{ast => sil}

/**
  * A hypothesis.
  */
case class Hypothesis(predicates: Map[String, sil.Predicate]) {
  def get(name: String): sil.Exp =
    predicates
      .get(name)
      .flatMap { predicate => predicate.body }
      .getOrElse(sil.TrueLit()())

  def get(instance: Instance): sil.Exp = {
    val body = get(instance.name)
    instance.toActual(body)
  }
}