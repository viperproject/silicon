/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silicon.state.State
import viper.silver.components.StatefulComponent

trait VerificationUnit[U <: ast.Node] extends StatefulComponent {
  def units: Seq[U]
  def verify(s: State, unit: U): Seq[VerificationResult]
}
