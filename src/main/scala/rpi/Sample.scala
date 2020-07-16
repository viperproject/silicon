package rpi

import viper.silver.ast.FieldAccess

sealed trait Sample

case class Record(vector: Seq[Boolean], access: FieldAccess)

case class Positive(record: Record) extends Sample

case class Negative(record: Record) extends Sample

case class Implication(left: Record, right: Record) extends Sample