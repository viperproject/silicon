// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.{Implies, Term, True, Var, perms}
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.{NegativePermission, NonPositivePermission}

object permissionSupporter extends SymbolicExecutionRules {
  /** @param cond Guard under which the permission amount has to be non-negative. Callers that
    *             produce a resource unconditionally leave this at `True`; callers that only
    *             conditionally gain the permission (see the lazy impure implication handling in
    *             [[producer]]) pass the guard, so that a permission amount which is only
    *             non-negative under that guard is not rejected. */
  def assertNotNegative(s: State, tPerm: Term, ePerm: ast.Exp, ePermNew: Option[ast.Exp], pve: PartialVerificationError, v: Verifier, cond: Term = True)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        val assertTerm = Implies(cond, perms.IsNonNegative(tPerm))
        v.decider.assert(assertTerm) {
          case true => Q(s, v)
          case false =>
            val assertExp = ePermNew.map(ep => perms.IsNonNegative(ep)(ep.pos, ep.info, ep.errT))
            createFailure(pve dueTo NegativePermission(ePerm), v, s, assertTerm, assertExp)
        }
    }
  }

  def assertPositive(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        v.decider.assert(perms.IsPositive(tPerm)) {
          case true => Q(s, v)
          case false => createFailure(pve dueTo NonPositivePermission(ePerm), v, s, perms.IsPositive(tPerm), Option.when(withExp)(perms.IsPositive(ePerm)()))
        }
    }
  }
}
