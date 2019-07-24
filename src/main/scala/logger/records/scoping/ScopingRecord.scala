package logger.records.scoping

import logger.records.{RecordData, SymbolicRecord}

trait ScopingRecord extends SymbolicRecord {
  val refId: Int
  var timeMs: Long = 0

  override def getData(): RecordData = {
    val data = super.getData()
    data.refId = Some(refId)
    data.timeMs = Some(timeMs)
    data
  }
}
