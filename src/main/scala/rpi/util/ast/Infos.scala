package rpi.util.ast

import viper.silver.ast

object ValueInfo {
  def valueOption[T](node: ast.Infoed): Option[T] =
    node
      .info
      .getUniqueInfo[ValueInfo[T]]
      .map { info => info.value }

  def value[T](node: ast.Infoed): T =
    valueOption(node).get
}

/**
  * An info holding a value.
  *
  * @param value The value.
  * @tparam T The type of the value.
  */
case class ValueInfo[+T](value: T) extends ast.Info {
  override def comment: Seq[String] =
    Seq.empty

  override def isCached: Boolean = false
}

/**
  * A mixin that enables comments.
  */
trait Comment extends ValueInfo[Any] {
  override def comment: Seq[String] =
    Seq(value.toString)
}