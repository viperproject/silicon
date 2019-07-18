package logger.renderer

import logger.{GenericBranchInfo, GenericNode, SymbLog}
import logger.records.SymbolicRecord
import logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import logger.records.structural.{BranchInfo, BranchingRecord, JoiningRecord}

class GenericNodeRenderer extends Renderer[SymbLog, List[GenericNode]] {

  def render(memberList: List[SymbLog]): List[GenericNode] = {
    memberList
      .map(renderMember)
      .foldLeft(List[GenericNode]())((prevVal, curVal) => prevVal ++ curVal)
  }

  def renderMember(s: SymbLog): List[GenericNode] = {
    var res = List[GenericNode]()

    for (record <- s.log) {
      res = res :+ renderRecord(record)
    }

    res
  }

  def renderRecord(record: SymbolicRecord): GenericNode = {
    val node = new GenericNode(record.id, record.toString)
    node.data = record.getNodeData()

    record match {
      case br: BranchingRecord => node.branches = br.getBranchInfos().map(renderBranch)
      case jr: JoiningRecord => node.isJoinPoint = true
      case os: OpenScopeRecord => node.isScopeOpen = true
      case cs: CloseScopeRecord => node.isScopeClose = true
      case _ =>
    }

    node
  }

  def renderBranch(info: BranchInfo): GenericBranchInfo = {
    new GenericBranchInfo(
      info.isReachable,
      info.startTimeMs,
      info.records.map(renderRecord))
  }
}
