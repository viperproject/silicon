package logger.records.scoping

class CloseScopeRecord(val refId: Int) extends ScopingRecord {

  override def toTypeString(): String = {
    "close"
  }

  override def toSimpleString(): String = {
    refId.toString
  }
}
