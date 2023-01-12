// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.state._
import viper.silicon.state.terms._

object functionSupporter {
  def limitedVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "limited")
    HeapDepFun(id, function.argSorts, function.resultSort)
  }

  def statelessVersion(function: HeapDepFun): Fun = {
    val id = function.id.withSuffix("%", "stateless")
    Fun(id, function.argSorts.tail, terms.sorts.Bool)
  }

  def preconditionVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "precondition")
    HeapDepFun(id, function.argSorts, terms.sorts.Bool)
  }
}
