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
import viper.silicon.state.terms.{Term, perms, Var}
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.NegativePermission

object permissionSupporter extends SymbolicExecutionRules {
  def assertNotNegative(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        v.decider.assert(perms.IsNonNegative(tPerm)) {
          case true => Q(s, v)
          case false => createFailure(pve dueTo NegativePermission(ePerm), v, s)
        }
    }
  }
}
