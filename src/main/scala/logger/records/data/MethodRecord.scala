package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class MethodRecord(v: ast.Method, s: State, p: PathConditionStack) extends MemberRecord {
  val value: ast.Method = v
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "method"
  }

  override def toSimpleString(): String = {
    if (value != null) value.name
    else "null"
  }
}
