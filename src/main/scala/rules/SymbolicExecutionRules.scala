// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.interfaces.Failure
import viper.silicon.interfaces.state.Chunk
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{BackendSpecificCounterexample, Model, ModelEntry, VerificationError}

import scala.collection.mutable

case class SiliconCounterexample(store: Map[String, Term], heap: Iterable[Chunk], oldHeap: Iterable[Chunk], nativeModel: Model) extends BackendSpecificCounterexample

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
      val store = s.g.values.map(entry => entry._1.name -> entry._2)
      ve.counterExample = Some(SiliconCounterexample(store, s.h.values, s.oldHeaps(Verifier.PRE_STATE_LABEL).values, nativeModel))
      ve.scope = s.currentMember
    }
    Failure(ve)
  }
}