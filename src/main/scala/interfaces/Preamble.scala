/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon.Set
import viper.silicon.state.terms.Sort

trait PreambleEmitter extends StatefulComponent {
  def analyze(program: ast.Program)
  def sorts: Set[Sort]
  def declareSorts()
  def declareSymbols()
  def emitAxioms()
}
