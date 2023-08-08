package viper.silicon.logger.benchmarker

import viper.silicon.logger.MemberSymbExLogger
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.writer.SymbExLogReportWriter
import viper.silicon.logger.MemberSymbExLog

object SymbExLogBenchmarker {
  def analyse(l: SymbExLogger[_ <: MemberSymbExLogger]): Unit = {
    for (log <- l.logs) {
      val allRecords = SymbExLogReportWriter.getAllRecords(log.asInstanceOf[MemberSymbExLog].log)
      for (rec <- allRecords) {
        println(rec.getClass())
      }
    }
  }
}

