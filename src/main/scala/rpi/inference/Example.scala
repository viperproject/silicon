package rpi.inference

import rpi.util.Expressions
import viper.silver.ast

/**
  * The super trait for all examples.
  */
trait Example

/**
  * A positive example.
  * @param records The records.
  */
case class PositiveExample(records: Seq[Record]) extends Example

/**
  * A negative example.
  *
  * @param record The records.
  */
case class NegativeExample(record: Record) extends Example

/**
  * An implication example.
  *
  * @param left  The left-hand side of the implication.
  * @param right The right-hand side of the implication.
  */
case class ImplicationExample(left: Record, right: Seq[Record]) extends Example

/**
  * A record representing a data pont.
  * @param specification The specification.
  * @param abstraction   The state abstraction.
  * @param locations     The (under-approximate) set of location accesses that can be used to represent the resource for
  *                      which permissions are required.
  */
case class Record(specification: Specification, abstraction: Abstraction, locations: Set[ast.LocationAccess]) {
  override def toString: String = s"${specification.name}: $abstraction -> {${locations.mkString(", ")}}"
}

/**
  * An abstraction of a snapshot that describes the set of concrete states that evaluate the given atoms to the given
  * values.
  *
  * TODO: A canonical form for atoms could allow us to recognize equivalent expressions.
  */
case class Abstraction(values: Map[ast.Exp, Boolean]) {
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

  @inline
  def getValue(expression: ast.Exp): Option[Boolean] =
    values.get(expression)

  /**
    * Returns the values of the given atoms in the abstract state.
    *
    * @param atoms The atoms.
    * @return The values of the atoms.
    */
  def getValues(atoms: Seq[ast.Exp]): Seq[Option[Boolean]] =
    atoms.map { atom => values.get(atom) }

  override def toString: String =
    values
      .map { case (atom, value) => if (value) atom else Expressions.not(atom) }
      .mkString("{", ", ", "}")
}
