// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.structural

import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.state.terms.Term
import viper.silver.ast.Exp

class BranchingRecord(possibleBranchesCount: Int, val condition: Option[Term], val conditionExp: Option[Exp]) extends StructuralRecord {
  private var currentBranchIndex = 0
  private val branches: Vector[BranchInfo] = Vector.tabulate(possibleBranchesCount)(_ => new BranchInfo())

  def getCurrentBranch: BranchInfo = {
    assert(0 <= currentBranchIndex && currentBranchIndex < branches.length)
    branches(currentBranchIndex)
  }

  def appendLog(r: SymbolicRecord): Unit =
    getCurrentBranch.records :+= r

  def markReachable(): Unit = {
    getCurrentBranch.isReachable = true
    getCurrentBranch.startTimeMs = System.currentTimeMillis()
  }

  def switchToNextBranch(): Unit = {
    currentBranchIndex = currentBranchIndex + 1
  }

  def getBranches: Vector[Seq[SymbolicRecord]] = {
    branches.map(log => log.records)
  }

  def getBranchInfos: Vector[BranchInfo] = {
    branches
  }

  def isReachable(branchIndex: Int): Boolean = {
    assert(branchIndex < branches.length)
    branches(branchIndex).isReachable
  }

  override val toTypeString: String = "branching"

  override lazy val toSimpleString: String = {
    condition match {
      case Some(cond) => cond.toString()
      case _ => "null"
    }
  }
}

class BranchInfo {
  var isReachable: Boolean = false
  var startTimeMs: Long = 0
  var records: Seq[SymbolicRecord] = Seq[SymbolicRecord]()
}
