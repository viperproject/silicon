/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.decider

import viper.silicon.state.terms.{Term, Sort, Decl}

trait TermConverter[T, S, D] {
  def convert(term: Term): T
  def convert(sort: Sort): S
  def convert(decl: Decl): D
}
