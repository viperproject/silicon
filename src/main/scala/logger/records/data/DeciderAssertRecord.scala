package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class DeciderAssertRecord(val term: Term, val timeout: Option[Int]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = null

  override def toTypeString(): String = {
    "decider assert"
  }

  override def toSimpleString(): String = {
    if (term != null) term.toString()
    else "null"
  }
}
