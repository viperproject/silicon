package rpi

import viper.silver.ast.LocationAccess

sealed trait Sample

case class Record(access: LocationAccess)

case class Positive(record: Record) extends Sample

case class Negative(record: Record) extends Sample

case class Implication(left: Record, right: Record) extends Sample