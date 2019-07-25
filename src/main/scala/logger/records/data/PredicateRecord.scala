package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class PredicateRecord(v: ast.Predicate, s: State, p: PathConditionStack) extends MemberRecord {
  val value: ast.Predicate = v
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "predicate"
  }

  override def toSimpleString(): String = {
    if (value != null) value.name
    else "null"
  }
}
