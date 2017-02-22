/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.state._
import viper.silicon.state.terms._

object functionSupporter extends Immutable {
  def limitedVersion(function: HeapDepFun): HeapDepFun = {
    val id = function.id.withSuffix("%", "limited")
    HeapDepFun(id, function.argSorts, function.resultSort)
  }

  def statelessVersion(function: HeapDepFun): Fun = {
    val id = function.id.withSuffix("%", "stateless")
    Fun(id, function.argSorts.tail, terms.sorts.Bool)
  }
}
