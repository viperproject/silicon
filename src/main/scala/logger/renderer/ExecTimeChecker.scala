package logger.renderer

import logger.SymbLog
import logger.records.SymbolicRecord
import logger.records.data.DataRecord
import logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import logger.records.structural.BranchingRecord

class ExecTimeChecker extends Renderer[SymbLog, String] {
  def render(memberList: List[SymbLog]): String = {
    var res = List[String]()
    for (m <- memberList) {
      res = res :+ renderMember(m)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderMember(member: SymbLog): String = {
    checkRecord(member.log, List[SymbolicRecord]())._1.mkString("\n")
  }

  def checkRecord(log: List[SymbolicRecord], initRecords: List[SymbolicRecord]): (List[String], List[SymbolicRecord]) = {
    var checks = List[String]()
    var records = initRecords

    for (logIndex <- log.indices) {
      val currentRecord: SymbolicRecord = log(logIndex)
      val nextRecord: SymbolicRecord = if (logIndex < log.length - 1) log(logIndex + 1) else null
      currentRecord match {
        case dr: DataRecord => {
          nextRecord match {
            case os: OpenScopeRecord => {
              if (dr.id != os.refId) {
                checks = checks :+ "invalid ref in OpenScopeRecord after " + dr.toString()
              } else {
                records = records :+ dr
              }
            }
            case _ =>
          }
        }
        case cs: CloseScopeRecord => {
          val dataRecordCount = records.count(dr => dr.id == cs.refId)
          assert(dataRecordCount == 1)
          records = records.filterNot(dr => dr.id == cs.refId)
        }
        case br: BranchingRecord => {
          records = records :+ br
          val reachableBranches = br.getBranches().zipWithIndex
            .filter({
              case (_, branchIndex) => br.isReachable(branchIndex)
            }).map({
              case (branch, _) => branch
            })
          val res = reachableBranches.map(branch => checkRecord(branch, records))
          checks = res.foldLeft(checks)((prevVal, curVal) => prevVal ++ curVal._1)
          val equalLength = res.map(r => r._2)
            .forall(p => p.length == res.head._2.length)
          if (!equalLength) {
            checks = checks :+ "branches of " + br.toString + " have different scopes"
          }
          for (branchRes <- res) {
            for (recIndex <- 0 until Math.min(res.head._2.length, branchRes._2.length)) {
              val expected = res.head._2(recIndex)
              val actual = branchRes._2(recIndex)
              if (expected.id != actual.id) {
                checks = checks :+ "data records (" + expected.id + ") of " + br.toString + " have different order"
              }
            }
          }
          if (res.nonEmpty) {
            // otherwise all branches are unreachable and hence keep records unchanged
            records = res.head._2
          }
        }
        case _ =>
      }
    }

    (checks, records)
  }
}
