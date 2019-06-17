package logger.records.data

import logger.records.SymbolicRecord
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

trait DataRecord extends SymbolicRecord {
  val value: ast.Node
  val state: State
  // TODO: It would be nicer to use the PathConditionStack instead of the
  // Decider's internal representation for the pcs.
  // However, the recording happens to early such that the wrong
  // PathConditionStack Object is stored when using the PathConditionStack
  // TODO: Oops.
  val pcs: Set[Term]

  override def toString(): String = {
    toTypeString() + " " + toSimpleString()
  }

  def toTypeString(): String

  def toSimpleString(): String = {
    if (value != null) value.toString()
    else "null"
  }
}
