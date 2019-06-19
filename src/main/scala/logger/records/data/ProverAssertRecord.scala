package logger.records.data

import logger.GenericNodeData
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class ProverAssertRecord(val term: Term, val timeout: Option[Int]) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: Set[Term] = null

  override def toTypeString(): String = {
    "prover assert"
  }

  override def toSimpleString(): String = {
    if (term != null) term.toString()
    else "null"
  }

  override def getNodeData(): GenericNodeData = {
    val data = super.getNodeData()
    data.isSmtQuery = true
    data
  }
}
