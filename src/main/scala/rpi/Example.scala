package rpi

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
  * @param predicate The predicate representing the inferred specifications this data point refers to.
  * @param state     The abstract state.
  * @param locations The (under-approximate) set of location accesses that can ber used to represent the location for
  *                  which some permissions are required.
  */
case class Record(predicate: sil.PredicateAccess, state: AbstractState, locations: Set[sil.LocationAccess]) {
  override def toString: String =
    s"${predicate.predicateName}: $state -> ${locations.mkString("{", ", ", "}")}"
}

/**
  * An abstract state that abstracts the set of concrete state where some set of expressions evaluates to specific
  * values.
  *
  * TODO: Canonical form for atoms (to recognize stuff that is equivalent).
  * TODO: Replace pairs with map and avoid duplicates.
  *
  * @param pairs The pairs associating expressions with their value.
  */
case class AbstractState(pairs: Seq[(sil.Exp, Boolean)]) {
  private lazy val map = pairs.toMap

  def meet(other: AbstractState): AbstractState =
    AbstractState(pairs ++ other.pairs)

  def getValues(atoms: Seq[sil.Exp]): Seq[Boolean] =
    atoms.map { atom => map(atom) }

  override def toString: String =
    pairs
      .map { case (atom, value) => if (value) atom else Expressions.negate(atom) }
      .mkString("{", ",", "}")
}