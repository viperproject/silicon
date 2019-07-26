package viper.silicon.logger.records

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.Map
import viper.silicon.state.{Heap, Store}
import viper.silicon.state.terms.Term

class RecordData {
  var refId: Option[Int] = None
  var isSmtQuery: Boolean = false
  var smtStatistics: Option[Map[String, String]] = None
  var timeMs: Option[Long] = None
  var pos: Option[String] = None
  var lastSMTQuery: Option[Term] = None
  var store: Option[Store] = None
  var heap: Option[Heap] = None
  var oldHeap: Option[Heap] = None
  var pcs: Option[InsertionOrderedSet[Term]] = None
}
