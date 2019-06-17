package logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class WellformednessCheckRecord(v: Seq[ast.Exp], s: State, p: PathConditionStack) extends DataRecord {
  val value: ast.Node = null
  val conditions: Seq[ast.Exp] = v
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "WellformednessCheck"
  }
}
