// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.biabduction.{AbductionResult, BiAbductionSolver, SiliconAbductionQuestion}
import viper.silicon.interfaces.{Failure, SiliconFailureContext, SiliconMappedCounterexample, SiliconNativeCounterexample, SiliconVariableCounterexample}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.ast.{AccessPredicate, FieldAccess, FieldAccessPredicate, FullPerm, PredicateAccess, PredicateAccessPredicate}
import viper.silver.frontend.{MappedModel, NativeModel, VariablesModel}
import viper.silver.verifier.errors.ErrorWrapperWithTransformers
import viper.silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
import viper.silver.verifier.{AbductionQuestionTransformer, Counterexample, CounterexampleTransformer, VerificationError}

trait SymbolicExecutionRules {
  protected def createFailure(ve: VerificationError, v: Verifier, s: State, generateNewModel: Boolean = false): Failure = {
    if (s.retryLevel == 0 && !ve.isExpected) v.errorsReportedSoFar.incrementAndGet()
    var ceTrafo: Option[CounterexampleTransformer] = None
    var aqTrafo: Option[AbductionQuestionTransformer] = None
    val res = ve match {
      case ErrorWrapperWithTransformers(wrapped, ceTra, aqTra) =>
        ceTrafo = Some(ceTra)
        aqTrafo = Some(aqTra)
        wrapped
      case _ => ve
    }
    if (v != null && (Verifier.config.reportReasonUnknown() || Verifier.config.counterexample.toOption.isDefined)) {
      if (generateNewModel || !v.decider.hasModel()) {
        v.decider.generateModel()
      }
    }
    val counterexample: Option[Counterexample] = if (v != null && Verifier.config.counterexample.toOption.isDefined) {
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

    val reasonUnknown = if (v != null && Verifier.config.reportReasonUnknown()) {
      Some(v.decider.prover.getReasonUnknown())
    } else {
      None
    }

    val branchconditions = if (Verifier.config.enableBranchconditionReporting()) {
      v.decider.pcs.branchConditionExps.flatten
        .filterNot(e => e.isInstanceOf[viper.silver.ast.TrueLit]) /* remove "true" bcs introduced by viper.silicon.utils.ast.BigAnd */
        .sortBy(_.pos match {
          /* Order branchconditions according to source position */
          case pos: viper.silver.ast.HasLineColumn => (pos.line, pos.column)
          case _ => (-1, -1)
        })
    } else Seq()

    val abdGoal: Option[AccessPredicate] = ve.reason match {
      case reason: InsufficientPermission =>
        val acc = reason.offendingNode match {
          case n: FieldAccess => FieldAccessPredicate(n, FullPerm()())()
          case n: PredicateAccess => PredicateAccessPredicate(n, FullPerm()())()
        }
        Some(acc)
      case reason: MagicWandChunkNotFound => Some(reason.offendingNode)
      case _ => None
    }
    val abductionResult = abdGoal.map{acc => BiAbductionSolver.solve(s, v, Seq(acc), aqTrafo)}

    res.failureContexts = Seq(SiliconFailureContext(branchconditions, counterexample, reasonUnknown, abductionResult))
    Failure(res, v.reportFurtherErrors())

  }
}
