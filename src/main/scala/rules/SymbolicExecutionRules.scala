// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.interfaces.{Failure, SiliconDebuggingFailureContext, SiliconFailureContext, SiliconMappedCounterexample, SiliconNativeCounterexample, SiliconSmtStateContext, SiliconVariableCounterexample}
import viper.silicon.state.State
import viper.silicon.state.terms.{False, Term}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.frontend.{MappedModel, NativeModel, VariablesModel}
import viper.silver.verifier.errors.ErrorWrapperWithExampleTransformer
import viper.silver.verifier.{Counterexample, CounterexampleTransformer, VerificationError}
import viper.silver.reporter.BlockFailureMessage

trait SymbolicExecutionRules {
  lazy val withExp = Verifier.config.enableDebugging()

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, failedAssert: Term, failedAssertDescription: String, generateNewModel: Boolean): Failure = {
    createFailure(ve, v, s, failedAssert, Option.when(withExp)(DebugExp.createInstance(failedAssertDescription)), generateNewModel)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, failedAssert: Term, failedAssertDescription: String): Failure = {
    createFailure(ve, v, s, failedAssert, Option.when(withExp)(DebugExp.createInstance(failedAssertDescription)), false)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, missingTermDescription: String): Failure = {
    createFailure(ve, v, s, False, Option.when(withExp)(DebugExp.createInstance(s"Asserted term for '$missingTermDescription' not available, substituting false.")), false)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, missingTermDescription: String, generateNewModel: Boolean): Failure = {
    createFailure(ve, v, s, False, Option.when(withExp)(DebugExp.createInstance(s"Asserted term for '$missingTermDescription' not available, substituting false.")), generateNewModel)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, failedAssert: Term, failedAssertExp: Option[ast.Exp]): Failure = {
    createFailure(ve, v, s, failedAssert, Option.when(withExp)(DebugExp.createInstance(failedAssertExp, failedAssertExp)), false)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, failedAssert: Term, generateNewModel: Boolean, failedAssertExp: Option[ast.Exp]): Failure = {
    createFailure(ve, v, s, failedAssert, Option.when(withExp)(DebugExp.createInstance(failedAssertExp, failedAssertExp)), generateNewModel)
  }

  protected def createFailure(ve: VerificationError, v: Verifier, s: State, failedAssert: Term, failedAssertExp: Option[DebugExp], generateNewModel: Boolean): Failure = {
    if (s.retryLevel == 0 && !ve.isExpected) {
      if (Verifier.config.generateBlockMessages()) {
        s.currentMember.foreach((member) => {
          val memberName = member.name
          s.currentBlock.foreach((block) => 
            v.reporter.report(BlockFailureMessage(memberName, block._1, block._2))
          )
        })
      }

      v.errorsReportedSoFar.incrementAndGet()
    }

    var ceTrafo: Option[CounterexampleTransformer] = None
    val res = ve match {
      case ErrorWrapperWithExampleTransformer(wrapped, trafo) =>
        ceTrafo = Some(trafo)
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

    /* Rlimit spent on the failing check itself; same last-assert adjacency
     * assumption as reasonUnknown above. */
    val rlimitDelta = if (v != null) v.decider.prover.getLastRlimitDelta() else None

    val branchconditions = if (Verifier.config.enableBranchconditionReporting()) {
      v.decider.pcs.branchConditionExps.map(_._1)
        .filterNot(e => e.isInstanceOf[viper.silver.ast.TrueLit]) /* remove "true" bcs introduced by viper.silicon.utils.ast.BigAnd */
    } else Seq()

    if (Verifier.config.enableDebugging()){
      val assumptions = v.decider.pcs.assumptionExps
      val debugCtx = SiliconDebuggingFailureContext(v.decider.pcs.branchConditions, v.decider.pcs.branchConditionExps.map(bce => bce._1 -> bce._2.get),
        counterexample, reasonUnknown, Some(s), Some(v), v.decider.prover.getAllEmits(), v.decider.prover.preambleAssumptions,
        v.decider.macroDecls, v.decider.functionDecls, assumptions, failedAssert, failedAssertExp.get)
      res.failureContexts = Seq(debugCtx)
    } else if (Verifier.config.smtStateOnError()) {
      val stateCtx = SiliconSmtStateContext(v.decider.pcs.branchConditions,
        counterexample, reasonUnknown, rlimitDelta, Some(s), v.decider.prover.getAllEmits(), v.decider.prover.preambleAssumptions,
        v.decider.macroDecls, v.decider.functionDecls, v.decider.pcs.assumptions, failedAssert)
      res.failureContexts = Seq(stateCtx)
      /* Skip speculative attempts (retryLevel > 0) and expected errors*/
      if (s.retryLevel == 0 && !ve.isExpected)
        viper.silicon.reporting.SmtStateDumper.dump(res, stateCtx)
    } else {
      res.failureContexts = Seq(SiliconFailureContext(branchconditions, counterexample, reasonUnknown, rlimitDelta))
    }

    Failure(res, v.reportFurtherErrors())

  }
}
