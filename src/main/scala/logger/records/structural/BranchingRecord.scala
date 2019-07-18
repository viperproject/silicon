package logger.records.structural

import logger.records.SymbolicRecord

class BranchingRecord(possibleBranchesCount: Int) extends StructuralRecord {
  private var currentBranchIndex = 0
  private var branches: List[BranchInfo] = List.tabulate(possibleBranchesCount)(_ => new BranchInfo())

  private def getCurrentBranch(): BranchInfo = {
    assert(currentBranchIndex < branches.length)
    branches(currentBranchIndex)
  }

  def appendLog(r: SymbolicRecord): Unit = {
    assert(currentBranchIndex < branches.length)
    val branch = branches(currentBranchIndex)
    branch.records = branch.records :+ r
  }

  def markReachable(): Unit = {
    assert(currentBranchIndex < branches.length)
    val branch = branches(currentBranchIndex)
    branch.isReachable = true
    branch.startTimeMs = System.currentTimeMillis()
  }

  def switchToNextBranch(): Unit = {
    currentBranchIndex = currentBranchIndex + 1
  }

  def getBranches(): List[List[SymbolicRecord]] = {
    branches.map(log => log.records)
  }

  def getBranchInfos(): List[BranchInfo] = {
    branches
  }

  def isReachable(branchIndex: Int): Boolean = {
    assert(branchIndex < branches.length)
    branches(branchIndex).isReachable
  }

  override def toTypeString(): String = {
    "branching"
  }

  override def toSimpleString(): String = {
    branches.length.toString
  }
}

class BranchInfo {
  var isReachable: Boolean = false
  var startTimeMs: Long = 0
  var records: List[SymbolicRecord] = List[SymbolicRecord]()
}
