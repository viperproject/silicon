/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces.decider

import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon.decider.{Mark, PathConditionStack}
import viper.silicon.{Map, Set}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.interfaces.state.{Context, Store, Heap, State}
import viper.silicon.state.terms.{FullPerm, Term, Var, Sort, Function}

trait Decider[ST <: Store[ST],
              H <: Heap[H],
              S <: State[ST, H, S],
              C <: Context[C]]
    extends StatefulComponent {

  def prover: Prover

  def pcs: PathConditionStack
  def π: Set[Term]

  def checkSmoke(): Boolean

  def locally[R](block: (R => VerificationResult) => VerificationResult)
                (Q: R => VerificationResult)
                : VerificationResult

  def locally(block: => VerificationResult): VerificationResult

  def setCurrentBranchCondition(t: Term)
  def setPathConditionMark(): Mark

  def assume(t: Term)
  def assume(ts: Iterable[Term])

  def tryOrFail[R](σ: S, c: C)
                  (block:    (S, C, (R, C) => VerificationResult, Failure => VerificationResult)
                          => VerificationResult)
                  (Q: (R, C) => VerificationResult)
                  : VerificationResult

  def check(σ: S, t: Term, timeout: Int): Boolean
  def assert(σ: S, t: Term, timeout: Option[Int] = None)(Q: Boolean => VerificationResult): VerificationResult

  def fresh(id: String, sort: Sort): Var
  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function

  def fresh(sort: Sort): Var
  def fresh(v: ast.AbstractLocalVar): Var
  def freshARP(id: String = "$k", upperBound: Term = FullPerm()): (Var, Term)

  def statistics(): Map[String, String]
}
