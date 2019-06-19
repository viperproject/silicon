package logger.records.scoping

import logger.GenericNodeData
import logger.records.SymbolicRecord

trait ScopingRecord extends SymbolicRecord {
  val refId: Int
  var timeMs: Long = 0

  override def getNodeData(): GenericNodeData = {
    val data = super.getNodeData()
    data.refId = Some(refId)
    data.timeMs = Some(timeMs)
    data
  }
}
