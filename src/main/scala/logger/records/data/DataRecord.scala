// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.{RecordData, SymbolicRecord}
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silicon.utils
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.Positioned

trait DataRecord extends SymbolicRecord {
  val value: ast.Node
  val state: State
  // TODO: It would be nicer to use the PathConditionStack instead of the
  // Decider's internal representation for the pcs.
  // However, the recording happens to early such that the wrong
  // PathConditionStack Object is stored when using the PathConditionStack
  // TODO: Oops.
  val pcs: InsertionOrderedSet[Term]

  override lazy val toString: String = {
    s"${toTypeString} ${toSimpleString}"
  }

  override lazy val toSimpleString: String = {
    if (value != null) value.toString()
    else "null"
  }

  override def getData(): RecordData = {
    val data = super.getData()
    value match {
      case posValue: ast.Node with Positioned => data.pos = Some(utils.ast.sourceLineColumn(posValue))
      case _ =>
    }
    if (state != null) {
      if (SymbExLogger.logConfig.includeStore) {
        data.store = Some(state.g)
      }
      if (SymbExLogger.logConfig.includeHeap) {
        data.heap = Some(state.h)
      }
      if (SymbExLogger.logConfig.includeOldHeap) {
        data.oldHeap = state.oldHeaps.get(Verifier.PRE_STATE_LABEL)
      }
    }
    if (pcs != null && SymbExLogger.logConfig.includePcs) {
      data.pcs = Some(pcs)
    }
    data
  }
}
