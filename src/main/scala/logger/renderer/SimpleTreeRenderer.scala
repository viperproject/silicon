package logger.renderer

import logger.SymbLog
import logger.records.SymbolicRecord
import logger.records.data.DataRecord
import logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import logger.records.structural.{BranchingRecord, JoiningRecord}

class SimpleTreeRenderer extends Renderer[SymbLog, String] {
  def render(memberList: List[SymbLog]): String = {
    var res = ""
    for (m <- memberList) {
      res = res + renderMember(m) + "\n"
    }
    res
  }

  def renderMember(member: SymbLog): String = {
    val filteredLog = filterEmptyScopes(member.log)
    toSimpleTree(filteredLog, 0)
  }

  private def filterEmptyScopes(log: List[SymbolicRecord]): List[SymbolicRecord] = {
    var res = List[SymbolicRecord]()

    var logIndex = 0
    while (logIndex < log.length) {
      val currentRecord: SymbolicRecord = log(logIndex)
      val nextRecord: SymbolicRecord = if (logIndex < log.length - 1) log(logIndex + 1) else null
      if (nextRecord != null && discardBoth(currentRecord, nextRecord)) {
        logIndex = logIndex + 2
      } else {
        currentRecord match {
          case br: BranchingRecord => {
            br.branches = br.branches.map(filterEmptyScopes)
          }
          case _ =>
        }
        res = res :+ currentRecord
        logIndex = logIndex + 1
      }
    }

    res
  }

  private def discardBoth(currentRecord: SymbolicRecord, nextRecord: SymbolicRecord): Boolean = {
    // check if close scope record directly follows open scope record and both have same id:
    currentRecord match {
      case os: OpenScopeRecord => {
        nextRecord match {
          case cs: CloseScopeRecord => os.refId == cs.refId
          case _ => false
        }
      }
      case _ => false
    }
  }

  private def toSimpleTree(log: List[SymbolicRecord], n: Int): String = {
    var res = ""
    var indentLevel = n
    for (record <- log) {
      record match {
        case os: OpenScopeRecord => indentLevel = indentLevel + 1
        case cs: CloseScopeRecord => indentLevel = indentLevel - 1
        case br: BranchingRecord => res = res + toSimpleTree(br, indentLevel)
        case jr: JoiningRecord => res = res + toSimpleTree(jr, indentLevel)
        case dr: DataRecord => res = res + toSimpleTree(dr, indentLevel)
      }
    }
    res
  }

  private def getIndent(indentLevel: Int): String = {
    var indent = ""
    for (i <- 1 to indentLevel) {
      indent = "  " + indent
    }
    indent
  }

  private def toSimpleTree(dr: DataRecord, n: Int): String = {
    val indent = getIndent(n)
    indent + dr.toString() + "\n"
  }

  private def toSimpleTree(br: BranchingRecord, n: Int): String = {
    val indent = getIndent(n)
    var res = ""
    for (branchIndex <- br.branches.indices) {
      res = res + indent + "Branch " + (branchIndex + 1) + ":\n"
      val branch = br.branches(branchIndex)
      if (br.isUnreachable(branch)) {
        res = res + getIndent(n + 1) + "comment: Unreachable\n"
      } else {
        res = res + toSimpleTree(branch, n + 1)
      }
    }
    res
  }

  private def toSimpleTree(jr: JoiningRecord, n: Int): String = {
    getIndent(n) + "Join\n"
  }
}
