package logger.records.structural

import logger.records.SymbolicRecord
import logger.records.data.DataRecord

class BranchingRecord(val ref: DataRecord) extends StructuralRecord {
  type Log = List[SymbolicRecord]
  var branches: List[Log] = List[Log](List[SymbolicRecord]())

  def appendLog(r: SymbolicRecord): Unit = {
    assert(branches.nonEmpty)
    var currentBranch: Log = branches.last
    currentBranch = currentBranch :+ r
    branches = branches.init :+ currentBranch
  }

  def switchToNextBranch(): Unit = {
    branches = branches :+ List[SymbolicRecord]()
  }

  def isUnreachable(log: Log): Boolean = {
    var res = true
    for (record <- log) {
      record match {
        case dr: DataRecord => res = false
        case _ =>
      }
    }
    res
  }
}
