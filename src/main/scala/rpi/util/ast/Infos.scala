// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

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
      .getUniqueInfo[Previous]
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
  * Info object used to add information about what the previous value of an expression was.
  *
  * @param value The previous value.
  */
case class Previous(value: ast.Exp) extends InferenceInfo