package logger.records.scoping

import logger.records.data.DataRecord

class OpenScopeRecord(ref: DataRecord) extends ScopingRecord {
  val refId: Int = ref.id
}
