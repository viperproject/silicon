package logger.renderer

import viper.silicon.logger.SymbLog
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data.MemberRecord
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import viper.silicon.logger.records.structural.{BranchingRecord, JoiningRecord}
import viper.silicon.logger.renderer.Renderer

class StructuralTreeRenderer extends Renderer[SymbLog, String] {
  /** contains IDs of Joining- and MemberRecords such that indentation can be correctly calculated */
  var visibleRecordIds: Set[Int] = Set()

  def render(memberList: List[SymbLog]): String = {
    var res = ""
    for (m <- memberList) {
      res = res + renderMember(m) + "\n"
    }
    res
  }

  def renderMember(member: SymbLog): String = {
    toStructuralTree(member.log, 0)
  }

  private def toStructuralTree(log: List[SymbolicRecord], n: Int): String = {
    var res = ""
    var indentLevel = n
    for (record <- log) {
      record match {
        case os: OpenScopeRecord => if (visibleRecordIds.contains(os.refId)) indentLevel = indentLevel + 1
        case cs: CloseScopeRecord => if (visibleRecordIds.contains(cs.refId)) indentLevel = indentLevel - 1
        case br: BranchingRecord => res = res + toStructuralTree(br, indentLevel)
        case jr: JoiningRecord => res = res + toStructuralTree(jr, indentLevel)
        case mr: MemberRecord => res = res + toStructuralTree(mr, indentLevel)
        case _ =>
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

  private def toStructuralTree(mr: MemberRecord, n: Int): String = {
    visibleRecordIds = visibleRecordIds + mr.id
    val indent = getIndent(n)
    indent + mr.toString() + "\n"
  }

  private def toStructuralTree(br: BranchingRecord, n: Int): String = {
    val indent = getIndent(n)
    var res = ""
    val branches = br.getBranches()
    for (branchIndex <- branches.indices) {
      res = res + indent + "Branch " + (branchIndex + 1) + ":\n"
      val branch = branches(branchIndex)
      if (br.isReachable(branchIndex)) {
        res = res + getIndent(n + 1) + "comment: Reachable\n"
        res = res + toStructuralTree(branch, n + 1)
      } else {
        res = res + getIndent(n + 1) + "comment: Unreachable\n"
      }
    }
    res
  }

  private def toStructuralTree(jr: JoiningRecord, n: Int): String = {
    visibleRecordIds = visibleRecordIds + jr.id
    getIndent(n) + "Join\n"
  }
}
