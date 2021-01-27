package rpi.inference.annotation

import viper.silver.ast

/**
  * An annotation.
  *
  * @param name     The name.
  * @param argument The argument.
  */
case class Annotation(name: String, argument: ast.Exp) {
  override def toString: String = s"$name($argument)"
}
