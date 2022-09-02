// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.{Failure, SiliconFailureContext, SiliconMappedCounterexample, SiliconNativeCounterexample, SiliconVariableCounterexample}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.frontend.{MappedModel, NativeModel, VariablesModel}
import viper.silver.verifier.errors.ErrorWrapperWithExampleTransformer
import viper.silver.verifier.{Counterexample, CounterexampleTransformer, VerificationError}

trait SymbolicExecutionRules {
  protected def createFailure(ve: VerificationError, v: Verifier, s: State, generateNewModel: Boolean = false): Failure = {
    if (s.retryLevel == 0 && !ve.isExpected) v.errorsReportedSoFar.incrementAndGet()
    var ceTrafo: Option[CounterexampleTransformer] = None
    val res = ve match {
      case ErrorWrapperWithExampleTransformer(wrapped, trafo) =>
        ceTrafo = Some(trafo)
        wrapped
      case _ => ve
    }
    val counterexample: Option[Counterexample] = if (v != null && Verifier.config.counterexample.toOption.isDefined) {
      if (generateNewModel || !v.decider.hasModel()) {
        v.decider.generateModel()
      }
      if (v.decider.isModelValid()) {
        val nativeModel = v.decider.getModel()
        val ce_type = Verifier.config.counterexample()
        val ce: Counterexample = ce_type match {
          case NativeModel =>
            val oldHeaps = s.oldHeaps.map { case (label, heap) => label -> heap.values }
            SiliconNativeCounterexample(s.g, s.h.values, oldHeaps, nativeModel)
          case VariablesModel =>
            SiliconVariableCounterexample(s.g, nativeModel)
          case MappedModel =>
            SiliconMappedCounterexample(s.g, s.h.values, s.oldHeaps, nativeModel, s.program)
        }
        val finalCE = ceTrafo match {
          case Some(trafo) => trafo.f(ce)
          case _ => ce
        }
        Some(finalCE)
      } else None
    } else None

    val branchconditions = if (Verifier.config.enableBranchconditionReporting()) {
      v.decider.pcs.branchConditionExps.flatten
        .filterNot(e => e.isInstanceOf[viper.silver.ast.TrueLit]) /* remove "true" bcs introduced by viper.silicon.utils.ast.BigAnd */
        .sortBy(_.pos match {
          /* Order branchconditions according to source position */
          case pos: viper.silver.ast.HasLineColumn => (pos.line, pos.column)
          case _ => (-1, -1)
        })
    } else Seq()
    res.failureContexts = Seq(SiliconFailureContext(branchconditions, counterexample))
    Failure(res, v.reportFurtherErrors())

  }
}
