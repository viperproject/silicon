package viper.silicon.logger.benchmarker

import viper.silicon.logger.MemberSymbExLogger
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.writer.SymbExLogReportWriter
import viper.silicon.logger.MemberSymbExLog
import viper.silicon.logger.records.data.DeciderAssertRecord
import viper.silicon.logger.records.data.DeciderAssumeRecord
import viper.silicon.logger.records.data.ProverAssertRecord
import viper.silicon.logger.records.data.CommentRecord
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.logger.records.scoping.OpenScopeRecord
import viper.silicon.logger.records.scoping.CloseScopeRecord
//import viper.silicon.logger.LogConfig
//import spray.json.JsArray

object SymbExLogBenchmarker {

  def analyse(l: SymbExLogger[_ <: MemberSymbExLogger]): Unit = {
    //println(SymbExLogReportWriter.toJSON(l.logs.toSeq.asInstanceOf[Seq[MemberSymbExLog]], LogConfig.default()) : JsArray)
    var accumulated_times = scala.collection.mutable.Map[String, Long]()
    var running_times = scala.collection.mutable.Map[Int, (String, Long, Long)]()
    var num_branches = 0
    var to_open = ""
    for (log <- l.logs) {
      val allRecords = SymbExLogReportWriter.getAllRecords(log.asInstanceOf[MemberSymbExLog].log)
      for (rec <- allRecords) rec match {
        case _: DeciderAssertRecord | _: DeciderAssumeRecord | _:ProverAssertRecord | _:CommentRecord if !rec.isInstanceOf[CommentRecord] || rec.asInstanceOf[CommentRecord].toSimpleString == "push" || rec.asInstanceOf[CommentRecord].toSimpleString == "pop" =>
          to_open = "prover"
        case _: BranchingRecord =>
          num_branches += 1
          to_open = ""
        case s: OpenScopeRecord =>
          if (!to_open.isEmpty())
            running_times(s.refId) = (to_open, s.timeMs, s.timeMs)
        case s: CloseScopeRecord =>
          if (running_times contains s.refId) {
            val d: (String, Long, Long) = running_times(s.refId)
            accumulated_times(d._1) = (accumulated_times.getOrElse(d._1, 0): Long) - d._3 + d._2 + s.timeMs - d._2
          }
        case _ =>
          to_open = ""
      }
    }
    println(s"Prover time: ${accumulated_times("prover")}")
  }

}

