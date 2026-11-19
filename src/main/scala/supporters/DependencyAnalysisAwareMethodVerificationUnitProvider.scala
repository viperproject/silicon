// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.verifier.DependencyAnalysisAwareVerifier
import viper.silver.ast.Method

trait DependencyAnalysisAwareMethodVerificationUnitProvider extends DefaultMethodVerificationUnitProvider { v: DependencyAnalysisAwareVerifier =>
  override def methodSupporter: MethodSupporter = DependencyAnalysisAwareMethodSupporter

  private object DependencyAnalysisAwareMethodSupporter extends MethodSupporter {

    override def verify(sInit: State, method: Method): Seq[VerificationResult] = {

      addPreconditionNodes(method.pres)

      val result = super.verify(sInit, method)

      if (method.body.isEmpty)
        addDependenciesForAbstractMember(method.pres, method.posts)

      result foreach (attachIntraproceduralResult(_, method))

      result
    }
  }

}
