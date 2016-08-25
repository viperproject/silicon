/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silicon.interfaces.state.Heap
import viper.silicon.state.DefaultContext

trait VerificationUnit[H <: Heap[H], U <: ast.Node] extends PreambleEmitter {
  def units: Seq[U]
  def verify(unit: U, c: DefaultContext[H]): Seq[VerificationResult]
}
