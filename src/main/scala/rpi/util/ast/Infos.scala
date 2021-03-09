package rpi.util.ast

import viper.silver.ast

object Infos {
  def valueOption[T](node: ast.Infoed): Option[T] =
    node
      .info
      .getUniqueInfo[ValueInfo[T]]
      .map { info => info.value }

  def value[T](node: ast.Infoed): T =
    valueOption(node).get

  def isSaved(node: ast.Infoed): Boolean =
    node
      .info
      .getUniqueInfo[Saved.type]
      .isDefined
}

trait InferenceInfo extends ast.Info {
  override def comment: Seq[String] =
    Seq.empty

  override def isCached: Boolean =
    true
}

/**
  * An info holding a value.
  *
  * @param value The value.
  * @tparam T The type of the value.
  */
case class ValueInfo[+T](value: T) extends InferenceInfo

/**
  * A mixin that enables comments.
  */
trait Comment extends ValueInfo[Any] {
  override def comment: Seq[String] =
    Seq(value.toString)
}

/**
  * Info object used to tag saved variables that do not need to be evaluated in a particular state.
  */
case object Saved extends InferenceInfo