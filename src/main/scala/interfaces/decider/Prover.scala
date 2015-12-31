/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.decider

import viper.silver.components.StatefulComponent
import viper.silicon.Map
import viper.silicon.state.terms._

sealed abstract class Result
object Sat extends Result
object Unsat extends Result
object Unknown extends Result

trait Prover extends StatefulComponent {
  def termConverter: TermConverter[String, String, String] /* TODO: Should be type-parametric */
  def emit(content: String) /* TODO: Should be type-parametric */
  def assume(term: Term)
  def assert(goal: Term, timeout: Option[Int] = None): Boolean
  def check(timeout: Option[Int] = None): Result
  def logComment(str: String)
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function
  def declare(decl: Decl)
  def statistics(): Map[String, String]
  def proverRunStarts()
}
