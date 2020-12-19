package rpi.inference

import rpi.util.Expressions
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
case class Positive(record: Seq[Record]) extends Example

/**
  * A negative example.
  *
  * @param record The data point to exclude.
  */
case class Negative(record: Seq[Record]) extends Example

/**
  * An implication.
  *
  * @param left  The left-hand side of the implication.
  * @param right The right-hand side of the implication.
  */
case class Implication(left: Seq[Record], right: Seq[Record]) extends Example

/**
  * A data point.
  *
  * TODO: Add pointer to hole?
  *
  * @param specification The specification.
  * @param state         The abstract state.
  * @param locations     The (under-approximate) set of location accesses that can be used to represent the resource for
  *                      which some permissions are required.
  */
case class Record(specification: Specification, state: Abstraction, locations: Set[sil.LocationAccess]) {
  override def toString: String =
    s"${specification.name}: $state -> ${locations.map { location => s"$location" }.mkString("{", ", ", "}")}"
}

/**
  * An abstraction of a set that describes the set of concrete states where the given atoms evaluate to the given
  * values.
  *
  * TODO: A canonical form for atoms could allow us to recognize equivalent expressions.
  */
case class Abstraction(values: Map[sil.Exp, Boolean]) {
  /**
    * Computes the meet of this and the other abstract state.
    *
    * NOTE: The implementation assumes that the states are not conflicting,
    * i.e., do not assign different values to the same atom.
    *
    * @param other The other abstract state.
    * @return The meet.
    */
  def meet(other: Abstraction): Abstraction = {
    val combined = other.values.foldLeft(values) {
      case (map, (atom, value)) =>
        map.updated(atom, value)
    }
    Abstraction(combined)
  }

  /**
    * Returns the values of the given atoms in the abstract state.
    *
    * @param atoms The atoms.
    * @return The values of the atoms.
    */
  def getValues(atoms: Seq[sil.Exp]): Seq[Option[Boolean]] =
    atoms.map { atom => values.get(atom) }

  override def toString: String =
    values
      .map { case (atom, value) => if (value) atom else Expressions.not(atom) }
      .mkString("{", ", ", "}")
}