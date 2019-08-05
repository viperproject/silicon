package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.logger.records.RecordData
import viper.silicon.Map
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class ProverAssertRecord(val term: Term, val timeout: Option[Int]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = null
  var statistics: Option[Map[String, String]] = None

  override def toTypeString(): String = {
    "prover assert"
  }

  override def toSimpleString(): String = {
    if (term != null) term.toString()
    else "null"
  }

  override def getData(): RecordData = {
    val data = super.getData()
    data.isSmtQuery = true
    data.smtStatistics = statistics
    data
  }
}
