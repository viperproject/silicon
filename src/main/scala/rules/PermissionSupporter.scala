// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.rules

import viper.silicon.dependencyAnalysis.DependencyAnalysisInfos
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, Var, perms}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.{NegativePermission, NonPositivePermission}

object permissionSupporter extends SymbolicExecutionRules {
  def assertNotNegative(s: State, tPerm: Term, ePerm: ast.Exp, ePermNew: Option[ast.Exp], pve: PartialVerificationError, v: Verifier, analysisInfos: DependencyAnalysisInfos)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        val termToAssert = perms.IsNonNegative(tPerm)
        val debugExp = ePermNew.map(ep => perms.IsNonNegative(ep)(ep.pos, ep.info, ep.errT))
        v.decider.assert(termToAssert, analysisInfos) {
          case true => Q(s, v)
          case false =>
            val failure = createFailure(pve dueTo NegativePermission(ePerm), v, s, termToAssert, debugExp)
            if (s.retryLevel == 0) v.decider.handleFailedAssertion(termToAssert, debugExp, debugExp, analysisInfos, v.reportFurtherErrors())
            if (s.retryLevel == 0 && v.reportFurtherErrors()) failure combine Q(s, v) else failure
        }
    }
  }

  def assertPositive(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier, analysisInfos: DependencyAnalysisInfos)
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) =>
        Q(s, v)
      case _ =>
        val termToAssert = perms.IsPositive(tPerm)
        val debugExp = Option.when(withExp)(perms.IsPositive(ePerm)())
        v.decider.assert(termToAssert, analysisInfos) {
          case true => Q(s, v)
          case false =>
            val failure = createFailure(pve dueTo NonPositivePermission(ePerm), v, s, termToAssert, debugExp)
            if (s.retryLevel == 0) v.decider.handleFailedAssertion(termToAssert, debugExp, debugExp, analysisInfos, v.reportFurtherErrors())
            if (s.retryLevel == 0 && v.reportFurtherErrors()) failure combine Q(s, v) else failure
        }
    }
  }
}
