// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state.terms.Term
import viper.silver.ast

class FunctionRecord(v: ast.Function, p: PathConditionStack) extends MemberRecord {
  val value: ast.Function = v
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override val toTypeString: String = "function"

  override lazy val toSimpleString: String = {
    if (value != null) value.name
    else "null"
  }
}
