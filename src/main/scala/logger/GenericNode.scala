package logger

class GenericNode(val id: Int, val label: String) {

  var isJoinPoint: Boolean = false
  var isScopeOpen: Boolean = false
  var isScopeClose: Boolean = false
  var isSyntactic: Boolean = false
  var branches: List[List[GenericNode]] = _
  var data: GenericNodeData = _

  override def toString(): String = {
    label
  }
}

class GenericNodeData {
  var refId: Option[Int] = None
  var isSmtQuery: Boolean = false
  var timeMs: Option[Long] = None
}
