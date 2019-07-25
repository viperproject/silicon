package viper.silicon.logger.records

trait SymbolicRecord {
  var id: Int = -1

  override def toString(): String = {
    toTypeString() + " " + toSimpleString()
  }

  def toTypeString(): String

  def toSimpleString(): String

  def getData(): RecordData = {
    new RecordData()
  }
}
