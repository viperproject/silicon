package logger.records.scoping

import logger.records.data.DataRecord

class OpenScopeRecord(ref: DataRecord) extends ScopingRecord {
  val refId: Int = ref.id

  override def toTypeString(): String = {
    "open"
  }

  override def toSimpleString(): String = {
    refId.toString
  }
}
