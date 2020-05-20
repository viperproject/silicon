// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.Failure
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{Model, ModelEntry, VerificationError}

import scala.collection.mutable

trait SymbolicExecutionRules extends Immutable {
  protected def createFailure(ve: VerificationError, v: Verifier, s: State, generateNewModel: Boolean = false): Failure = {
    if (v != null && Verifier.config.counterexample.toOption.isDefined) {
      if (generateNewModel || v.decider.getModel() == null) {
        v.decider.generateModel()
      }
      val model = v.decider.getModel()
      val nativeModel = Model(model)
      val finalModel: Map[String, ModelEntry] = if (Verifier.config.counterexample.toOption.get == "native") nativeModel.entries else {
        val res = mutable.HashMap[String, ModelEntry]()
        for (curVar <- s.g.values) {
          if (nativeModel.entries.contains(curVar._2.toString)){
            res.update(curVar._1.name, nativeModel.entries.get(curVar._2.toString).get)
          }
        }
        res.toMap
      }
      ve.parsedModel = Some(Model(finalModel))
    }
    Failure(ve)
  }
}