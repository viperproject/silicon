package logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.state.NonQuantifiedChunk
import viper.silicon.state._
import viper.silicon.state.terms.Term
import viper.silver.ast

class SingleMergeRecord(val destChunks: Seq[NonQuantifiedChunk],
                        val newChunks: Seq[NonQuantifiedChunk],
                        p: PathConditionStack) extends DataRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override def toTypeString(): String = {
    "single merge"
  }

  override def toSimpleString(): String = {
    if (destChunks != null && newChunks != null) (destChunks ++ newChunks).mkString(" ")
    else "SingleMerge <null>"
  }
}
