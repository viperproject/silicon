package logger.records

import logger.GenericNodeData

trait SymbolicRecord {
  var id: Int = -1

  override def toString(): String = {
    toTypeString() + " " + toSimpleString()
  }

  def toTypeString(): String

  def toSimpleString(): String

  def getNodeData(): GenericNodeData = {
    new GenericNodeData()
  }
}
