// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

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
