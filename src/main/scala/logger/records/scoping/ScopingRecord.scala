package logger.records.scoping

import logger.records.SymbolicRecord

trait ScopingRecord extends SymbolicRecord {
  var timeMs: Long = 0
}
