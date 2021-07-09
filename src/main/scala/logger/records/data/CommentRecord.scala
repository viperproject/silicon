// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class CommentRecord(str: String, s: State, p: PathConditionStack) extends DataRecord {
  val value: ast.Node = null
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null
  val comment: String = str

  override val toTypeString: String = "comment"

  override lazy val toSimpleString: String = {
    if (comment != null) comment
    else "null"
  }

  override lazy val toString: String = {
    if (comment != null) {
      s"comment ${comment}"
    } else {
      "comment <null>"
    }
  }
}