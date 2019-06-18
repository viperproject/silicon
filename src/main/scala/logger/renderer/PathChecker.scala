package logger.renderer

import logger.records.SymbolicRecord
import logger.records.data.DataRecord
import logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import logger.records.structural.BranchingRecord

class PathChecker extends Renderer[MemberPath, String] {

  def render(memberList: List[MemberPath]): String = {
    var res = List[String]()
    for (m <- memberList) {
      res = res :+ renderMember(m)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderMember(s: MemberPath): String = {
    var res = List[String]()
    for (path <- s.paths) {
      res = res ++ renderPath(path)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderPath(path: List[SymbolicRecord]): List[String] = {
    var checks = List[String]()
    // check if each open scope has a single corrsponding close record
    // check if each branching record has a close scope record too
    var currentScope = List[SymbolicRecord]()

    for (record <- path) {
      record match {
        case dr: DataRecord => {
          if (countRecord(currentScope, dr.id) != 0) {
            checks = checks :+ "id " + dr.id + " already exists in the current scope"
          }
          currentScope = currentScope :+ dr
        }
        case br: BranchingRecord => {
          if (countRecord(currentScope, br.id) != 0) {
            checks = checks :+ "id " + br.id + " already exists in the current scope"
          }
          currentScope = currentScope :+ br
        }
        case os: OpenScopeRecord => {
          if (countRecord(currentScope, os.refId) != 1) {
            checks = checks :+ "refId " + os.refId + " not found for open scope record"
          }
        }
        case cs: CloseScopeRecord => {
          if (countRecord(currentScope, cs.refId) != 1) {
            checks = checks :+ "refId " + cs.refId + " not found for close scope record"
          }
          currentScope = removeRecord(currentScope, cs.refId)
        }
        case _ =>
      }
    }

    checks
  }

  private def countRecord(scope: List[SymbolicRecord], id: Int): Int = {
    var res = 0
    for (record <- scope) {
      if (record.id == id) {
        res = res + 1
      }
    }
    res
  }

  private def removeRecord(scope: List[SymbolicRecord], id: Int): List[SymbolicRecord] = {
    var res = List[SymbolicRecord]()
    for (record <- scope) {
      if (record.id != id) {
        res = res :+ record
      }
    }
    res
  }
}
