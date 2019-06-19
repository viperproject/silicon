package logger.records.structural

import logger.records.data.DataRecord
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class JoiningRecord(s: State, p: PathConditionStack) extends DataRecord with StructuralRecord {
  val value: ast.Node = null
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "joining"
  }
}
