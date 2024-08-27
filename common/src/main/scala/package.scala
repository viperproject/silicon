// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context

package object common {
  trait Mergeable[S <: Mergeable[S]] {
    def merge(other: S): S
  }
}

object Macros {
  //@inline
  //def when[T](cond: Boolean)(t: T): Option[T] = when2[T](cond, t)
  def when[T](cond: Boolean)(t: T): Option[T] = macro MacrosImpl.whenImpl[T]
}
class MacrosImpl(val c: Context) {
  import c.universe._

  def whenImpl[T: c.WeakTypeTag](cond: c.Expr[Boolean])(t: c.Expr[T]): c.Expr[Option[T]] =
    c.universe.reify {
      cond.splice match {
        case true => Some(t.splice)
        case false => None
      }
    }
}