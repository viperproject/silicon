package logger.renderer

import logger.SymbLog
import logger.records.SymbolicRecord
import logger.records.structural.BranchingRecord

class PathRenderer extends Renderer[SymbLog, List[MemberPath]] {

  private val keepBranchingRecords: Boolean = true

  def render(memberList: List[SymbLog]): List[MemberPath] = {
    memberList.map(member => renderMember(member).head)
  }

  def renderMember(s: SymbLog): List[MemberPath] = {
    List(new MemberPath(getPaths(s.log)))
  }

  def getPaths(records: List[SymbolicRecord]): List[List[SymbolicRecord]] = {
    var res = List[List[SymbolicRecord]](List[SymbolicRecord]())

    for (record <- records) {
      record match {
        case br: BranchingRecord => {
          val branchingResult = br.getBranches()
            .map(getPaths)
            .foldLeft(List[List[SymbolicRecord]]())((prevVal, curVal) => prevVal ++ curVal)
          // extend res to the same number of paths
          // insert each elem of branchingResult on a path
          val branchingPaths = branchingResult.map(branchRes => {
            if (keepBranchingRecords) {
              res.last ++ List(br) ++ branchRes
            } else {
              res.last ++ branchRes
            }
          })
          res = res.init ++ branchingPaths
        }
        case _ => {
          res = res.map(r => r :+ record)
        }
      }
    }

    res
  }
}

class MemberPath(val paths: List[List[SymbolicRecord]]) {

}
