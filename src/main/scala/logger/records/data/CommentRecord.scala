package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class CommentRecord(str: String, s: State, p: PathConditionStack) extends DataRecord {
  val value: ast.Node = null
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null
  val comment: String = str

  override def toTypeString(): String = {
    "comment"
  }

  override def toString(): String = {
    if (comment != null) {
      "comment " + comment
    } else {
      "comment <null>"
    }
  }
}
