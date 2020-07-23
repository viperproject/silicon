package rpi

/**
  * The super trait for all examples.
  */
trait Example

/**
  * A positive example.
  *
  * @param record The data point to include.
  */
case class Positive(record: Record) extends Example

/**
  * A negative example.
  *
  * @param record The data point not to include.
  */
case class Negative(record: Record) extends Example

/**
  * A data point.
  *
  * @param abstraction The predicate abstraction of the state.
  * @param access      The access path for which some permissions are required.
  */
case class Record(abstraction: Seq[Boolean], access: Seq[String]) {
  override def toString: String = {
    val absStr = abstraction.map(if (_) 1 else 0).mkString(",")
    val accStr = access.mkString(".")
    s"[$absStr] -> $accStr"
  }
}