package logger.records.data

import logger.records.RecordData
import viper.silicon.state.terms.Term

trait MemberRecord extends DataRecord {
  var lastFailedProverQuery: Option[Term] = None

  override def getData(): RecordData = {
    val data = super.getData()
    data.lastSMTQuery = lastFailedProverQuery
    data
  }
}
