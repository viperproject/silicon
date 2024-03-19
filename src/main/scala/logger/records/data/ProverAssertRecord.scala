// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.logger.records.RecordData
import viper.silicon.Map
import viper.silicon.logger.LogConfig
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class ProverAssertRecord(val term: Term, val timeout: Option[Int]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = null
  var statistics: Option[Map[String, String]] = None

  override val toTypeString: String = "prover assert"

  override lazy val toSimpleString: String = {
    if (term != null) term.toString
    else "null"
  }

  override def getData(config: LogConfig): RecordData = {
    val data = super.getData(config)
    data.isSmtQuery = true
    data.smtStatistics = statistics
    data
  }
}
