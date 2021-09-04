// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class SingleMergeRecord(val destChunks: Seq[NonQuantifiedChunk],
                        val newChunks: Seq[NonQuantifiedChunk],
                        p: PathConditionStack) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override val toTypeString: String = "single merge"

  override lazy val toSimpleString: String = {
    if (destChunks != null && newChunks != null) (destChunks ++ newChunks).mkString(" ")
    else "SingleMerge <null>"
  }

  override lazy val toString: String  = {
    if (destChunks != null && newChunks != null) {
      val newChunksString = newChunks.mkString(" ")
      if (newChunksString == "") {
        s"single merge ${destChunks.mkString(" ")} <="
      } else {
        s"single merge ${destChunks.mkString(" ")} <= $newChunksString"
      }
    } else {
      "SingleMerge <null>"
    }
  }
}
