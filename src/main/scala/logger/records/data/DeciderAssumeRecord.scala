package logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class DeciderAssumeRecord(val terms: InsertionOrderedSet[Term]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: Set[Term] = null

  override def toTypeString(): String = {
    "decider assume"
  }

  override def toSimpleString(): String = {
    if (terms != null) terms.mkString(" ")
    else "null"
  }
}
