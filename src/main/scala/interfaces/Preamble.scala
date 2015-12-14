/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package interfaces

import silver.ast
import silver.components.StatefulComponent
import silicon.state.terms.{Sort, Function}

trait PreambleEmitter extends StatefulComponent {
  def analyze(program: ast.Program)
  def sorts: Set[Sort]
  def symbols: Option[Set[Function]] /* TODO: Consider removing, doesn't appear to be useful */
  def declareSorts()
  def declareSymbols()
  def emitAxioms()
}
