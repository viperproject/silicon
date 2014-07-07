/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon
package interfaces.decider

import sil.components.StatefulComponent
import state.terms.{Sort, Decl, Term, Var}

sealed abstract class Result
object Sat extends Result
object Unsat extends Result
object Unknown extends Result

trait Prover extends StatefulComponent {
  def termConverter: TermConverter[String, String, String] /* TODO: Should be type-parametric */
  def assume(term: Term)
  def assert(goal: Term): Boolean
	def check(): Result
	def enableLoggingComments(enabled: Boolean)
	def logComment(str: String)
	def fresh(id: String, sort: Sort): Var
  def sanitizeSymbol(symbol: String): String
  def declare(decl: Decl)
  def statistics(): Map[String, String]
}
