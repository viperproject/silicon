package rpi

import viper.silver.ast.{Exp, FieldAccess, LocalVar, PredicateAccess}

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
  * An implication example.
  *
  * @param left  The left-hand side of the implication.
  * @param right The right-hand side of the implication.
  */
case class Implication(left: Record, right: Record) extends Example

/**
  * A data point.
  *
  * @param predicate   The predicate this data point refers to.
  * @param abstraction The predicate abstraction of the state.
  * @param accesses    The (under-approximate) set of access paths that can be used to represent the location for which
  *                    some permissions are required.
  */
case class Record(predicate: PredicateAccess, abstraction: Seq[Boolean], accesses: Set[AccessPath]) {
  override def toString: String = {
    val name = predicate.predicateName
    val absStr = abstraction.map(if (_) 1 else 0).mkString(",")
    val accStr = accesses.mkString(",")
    s"$predicate: [$absStr] -> {$accStr}"
  }
}

object AccessPath {
  def apply(exp: Exp): AccessPath = exp match {
    case LocalVar(name, _) => VariablePath(name)
    case FieldAccess(receiver, field) => FieldPath(AccessPath(receiver), field.name)
  }

  def apply(seq: Seq[String]): AccessPath = seq
    .tail.foldLeft[AccessPath](VariablePath(seq.head)) {
    case (receiver, field) => FieldPath(receiver, field)
  }
}

sealed trait AccessPath {
  def last: String = this match {
    case VariablePath(name) => name
    case FieldPath(_, name) => name
  }

  def dropLast: AccessPath = this match {
    case FieldPath(receiver, _) => receiver
    case _ => ???
  }

  def prefixes: Seq[AccessPath] = this match {
    case FieldPath(receiver, _) => receiver +: receiver.prefixes
    case _ => Seq.empty
  }

  def toSeq: Seq[String] = this match {
    case VariablePath(name) => Seq(name)
    case FieldPath(receiver, name) => receiver.toSeq :+ name
  }

  def length: Int = this match {
    case VariablePath(_) => 1
    case FieldPath(receiver, _) => receiver.length + 1
  }

  override def toString: String = toSeq.mkString(".")
}

case class VariablePath(name: String) extends AccessPath

case class FieldPath(receiver: AccessPath, name: String) extends AccessPath {
  override def toString: String = s"$receiver.$name"
}