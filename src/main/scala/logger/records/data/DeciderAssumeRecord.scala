// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class DeciderAssumeRecord(val terms: InsertionOrderedSet[Term]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = null

  override val toTypeString: String = "decider assume"

  override lazy val toSimpleString: String = {
    if (terms != null) terms.mkString(" ")
    else "null"
  }
}
