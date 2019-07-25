package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class CondExpRecord(v: ast.CondExp, s: State, p: PathConditionStack, val env: String) extends DataRecord {
  val value: ast.CondExp = v
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "conditional expression"
  }
}
