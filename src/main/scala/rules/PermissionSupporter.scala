// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.rules

import viper.silicon.dependencyAnalysis.DependencyAnalysisInfoes
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, Var, perms}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.{NegativePermission, NonPositivePermission}

object permissionSupporter extends SymbolicExecutionRules {
  def assertNotNegative(s: State, tPerm: Term, ePerm: ast.Exp, ePermNew: Option[ast.Exp], pve: PartialVerificationError, v: Verifier, analysisInfoes: DependencyAnalysisInfoes)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        v.decider.assert(perms.IsNonNegative(tPerm), analysisInfoes) {
          case true => Q(s, v)
          case false =>
            val assertExp = ePermNew.map(ep => perms.IsNonNegative(ep)(ep.pos, ep.info, ep.errT))
            val failure = createFailure(pve dueTo NegativePermission(ePerm), v, s, perms.IsNonNegative(tPerm), assertExp)
            if(s.retryLevel == 0) v.decider.handleFailedAssertionForDependencyAnalysis(perms.IsNonNegative(tPerm), analysisInfoes, v.reportFurtherErrors())
            if(s.retryLevel == 0 && v.reportFurtherErrors()) failure combine Q(s, v) else failure
        }
    }
  }

  def assertPositive(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier, analysisInfoes: DependencyAnalysisInfoes)
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        v.decider.assert(perms.IsPositive(tPerm), analysisInfoes) {
          case true => Q(s, v)
          case false =>
            val failure = createFailure(pve dueTo NonPositivePermission(ePerm), v, s, perms.IsPositive(tPerm), Option.when(withExp)(perms.IsPositive(ePerm)()))
            if(s.retryLevel == 0) v.decider.handleFailedAssertionForDependencyAnalysis(perms.IsPositive(tPerm), analysisInfoes, v.reportFurtherErrors())
            if(s.retryLevel == 0 && v.reportFurtherErrors()) failure combine Q(s, v) else failure
        }
    }
  }
}
