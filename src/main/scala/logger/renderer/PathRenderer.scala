package viper.silicon.logger.renderer

import viper.silicon.logger.SymbLog
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.structural.BranchingRecord

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
          // prepend each res to each branchingResult:
          // res does not need to have length 1 e.g. in case of joining
          res = res
            .map(r => branchingResult
              .map(branchRes => {
                if (keepBranchingRecords) {
                  r ++ List(br) ++ branchRes
                } else {
                  r ++ branchRes
                }
              }))
            .foldLeft(List[List[SymbolicRecord]]())((prevVal, curVal) => prevVal ++ curVal)
        }
        case _ => {
          // add it to all path in the current context:
          res = res.map(r => r :+ record)
        }
      }
    }

    res
  }
}

/**
  * Contains a list of records for each path of the corresponding member
  * @param paths
  */
class MemberPath(val paths: List[List[SymbolicRecord]]) {

}
