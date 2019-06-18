package logger.records.structural

import logger.records.SymbolicRecord
import logger.records.data.DataRecord

class BranchingRecord(val ref: DataRecord, possibleBranchesCount: Int) extends StructuralRecord {
  type Log = (Boolean, List[SymbolicRecord])
  private var currentBranchIndex = 0
  private var branches: List[Log] = List.fill(possibleBranchesCount)((false, List[SymbolicRecord]()))

  private def getCurrentLog(): Log = {
    assert(currentBranchIndex < branches.length)
    branches(currentBranchIndex)
  }

  private def updateCurrentLog(log: Log): Unit = {
    assert(currentBranchIndex < branches.length)
    val (lead, trail) = branches.splitAt(currentBranchIndex)
    branches = lead ++ List(log) ++ trail.tail
  }

  def appendLog(r: SymbolicRecord): Unit = {
    var currentBranch = getCurrentLog()
    currentBranch = (currentBranch._1, currentBranch._2 :+ r)
    updateCurrentLog(currentBranch)
  }

  def markReachable(): Unit = {
    var currentBranch = getCurrentLog()
    currentBranch = (true, currentBranch._2)
    updateCurrentLog(currentBranch)
  }

  def switchToNextBranch(): Unit = {
    currentBranchIndex = currentBranchIndex + 1
  }

  def getBranches(): List[List[SymbolicRecord]] = {
    branches.map(log => log._2)
  }

  def isReachable(branchIndex: Int): Boolean = {
    assert(branchIndex < branches.length)
    branches(branchIndex)._1
  }
}
