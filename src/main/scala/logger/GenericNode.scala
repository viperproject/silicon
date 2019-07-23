package logger

class GenericNode(val id: Int, val label: String) {

  var isJoinPoint: Boolean = false
  var isScopeOpen: Boolean = false
  var isScopeClose: Boolean = false
  var isSyntactic: Boolean = false
  var branches: List[GenericBranchInfo] = _
  var data: GenericNodeData = _

  override def toString(): String = {
    label
  }
}

class GenericBranchInfo(val isReachable: Boolean, val startTimeMs: Long, val records: List[GenericNode]) {

}

class GenericNodeData {
  var refId: Option[Int] = None
  var isSmtQuery: Boolean = false
  var timeMs: Option[Long] = None
  var pos: Option[String] = None
}
