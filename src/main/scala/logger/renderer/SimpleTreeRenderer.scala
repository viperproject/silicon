// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.renderer

import viper.silicon.logger.MemberSymbExLog
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data.DataRecord
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import viper.silicon.logger.records.structural.{BranchingRecord, JoiningRecord}
import viper.silicon.state.terms.Not

import scala.annotation.unused

class SimpleTreeRenderer extends Renderer[MemberSymbExLog, String] {
  def render(memberList: Iterable[MemberSymbExLog]): String = {
    var res = ""
    for (m <- memberList) {
      res = res + renderMember(m) + "\n"
    }
    res
  }

  def renderMember(member: MemberSymbExLog): String = {
    // val filteredLog = filterEmptyScopes(member.log)
    toSimpleTree(member.log, 0, 0)
  }

  /**
    *
    * @param log
    * @param minN specifies the minimal indentation level; this is necessary to ignore certain close scope records
    *             on a branch in order records on the branch have a higher indentation level than the branch indicator
    * @param n
    * @return
    */
  private def toSimpleTree(log: Seq[SymbolicRecord], minN: Int, n: Int): String = {
    var res = ""
    var indentLevel = n
    for (record <- log) {
      record match {
        case _: OpenScopeRecord => indentLevel = indentLevel + 1
        case _: CloseScopeRecord => indentLevel = Math.max(minN, indentLevel - 1)
        case br: BranchingRecord => res = res + toSimpleTree(br, minN, indentLevel)
        case jr: JoiningRecord => res = res + toSimpleTree(jr, minN, indentLevel)
        case dr: DataRecord => res = res + toSimpleTree(dr, minN, indentLevel)
      }
    }
    res
  }

  private def getIndent(indentLevel: Int): String = {
    "  " * indentLevel
  }

  private def toSimpleTree(dr: DataRecord, @unused minN: Int, n: Int): String = {
    val indent = getIndent(n)
    s"$indent$dr\n"
  }

  private def toSimpleTree(br: BranchingRecord, @unused minN: Int, n: Int): String = {
    val indent = getIndent(n)
    var res = ""
    val branches = br.getBranches
    for (branchIndex <- branches.indices) {
      if (branches.length <= 2 && br.condition.isDefined) {
        val condition = if (branchIndex == 0)  br.condition.get else Not(br.condition.get)
        res = s"${res}${indent}Branch ${condition}:\n"
      } else {
        res = s"${res}${indent}Branch ${branchIndex + 1}:\n"
      }
      val branch = branches(branchIndex)
      if (br.isReachable(branchIndex)) {
        res = s"${res}${getIndent(n + 1)}comment: Reachable\n"
        res = res + toSimpleTree(branch, n + 1, n + 1)
      } else {
        res = s"${res}${getIndent(n + 1)}comment: Unreachable\n"
      }
    }
    res
  }

  private def toSimpleTree(@unused jr: JoiningRecord, @unused minN: Int, n: Int): String = {
    s"${getIndent(n)}Join\n"
  }
}
