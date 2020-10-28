package rpi

import viper.silver.{ast => sil}

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
  * @param record The data point to exclude.
  */
case class Negative(record: Record) extends Example

/**
  * An implication example.
  *
  * @param left  The left-hand side of the implication.
  * @param right The right-hand side of the implication.
  */
case class Implication(left: Record, right: Record) extends Example

/**
  * A data point.
  *
  * @param predicate   The predicate representing the inferred specifications this data point refers to.
  * @param abstraction The predicate abstraction of the state.
  * @param locations   The (under-approximate) set of location accesses that can ber used to represent the location for
  *                    which some permissions are required.
  */
case class Record(predicate: sil.PredicateAccess, abstraction: Seq[Boolean], locations: Set[sil.LocationAccess]) {
  override def toString: String =
    s"${predicate.predicateName}: ${abstraction.mkString("[", ", ", "]")} -> ${locations.mkString("{", ", ", "}")}"
}