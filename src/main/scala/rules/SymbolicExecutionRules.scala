// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.{Failure, SiliconNativeCounterexample, SiliconVariableCounterexample}
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.verifier.errors.ErrorWrapperWithExampleTransformer
import viper.silver.verifier.{Counterexample, CounterexampleTransformer, Model, VerificationError}

trait SymbolicExecutionRules extends Immutable {
  protected def createFailure(ve: VerificationError, v: Verifier, s: State, generateNewModel: Boolean = false): Failure = {
    var ceTrafo: Option[CounterexampleTransformer] = None
    val res = ve match {
      case ErrorWrapperWithExampleTransformer(wrapped, trafo) => {
        ceTrafo = Some(trafo)
        wrapped
      }
      case _ => ve
    }
    if (v != null && Verifier.config.counterexample.toOption.isDefined) {
      if (generateNewModel || v.decider.getModel() == null) {
        v.decider.generateModel()
      }
      val model = v.decider.getModel()
      if (!model.contains("model is not available")){
        val nativeModel = Model(model)
        var ce: Counterexample = if (Verifier.config.counterexample.toOption.get == "native") {
          val oldHeap = if (s.oldHeaps.contains(Verifier.PRE_STATE_LABEL))
            Some(s.oldHeaps(Verifier.PRE_STATE_LABEL).values)
          else None
          SiliconNativeCounterexample(s.g, s.h.values, oldHeap, nativeModel)
        }else{
          SiliconVariableCounterexample(s.g, nativeModel)
        }
        val finalCE = ceTrafo match {
          case Some(trafo) => trafo.f(ce)
          case _ => ce
        }
        res.counterexample = Some(finalCE)
      }
    }
    Failure(res)

  }
}