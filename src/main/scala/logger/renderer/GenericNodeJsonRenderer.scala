package logger.renderer

import logger.{GenericNode, GenericNodeData}

class GenericNodeJsonRenderer extends JsonRenderer[GenericNode] {

  def render(memberList: List[GenericNode]): String = {
    val allNodes: List[GenericNode] = getAllNodes(memberList)
    val renderedMembers: Iterable[String] = allNodes.map(node => renderMember(node))
    "[" + renderedMembers.mkString(",") + "]"
  }

  def getAllNodes(r: List[GenericNode]): List[GenericNode] = {
    r.foldLeft(List[GenericNode]())((prevVal, curVal) => prevVal ++ getAllNodes(curVal))
  }

  def getAllNodes(r: GenericNode): List[GenericNode] = {
    if (r.branches != null) {
      r.branches.foldLeft(List(r))((prevVal, branch) => prevVal ++ getAllNodes(branch))
    } else {
      List(r)
    }
  }

  def renderMember(s: GenericNode): String = {
    val idJson = pair("id", s.id)
    val labelJson = pair("label", s.label)
    val isJoinPointJson = if (s.isJoinPoint) pair("isJoinPoint", s.isJoinPoint) else null
    val isScopeOpenJson = if (s.isScopeOpen) pair("isScopeOpen", s.isScopeOpen) else null
    val isScopeCloseJson = if (s.isScopeClose) pair("isScopeClose", s.isScopeClose) else null
    val isSyntacticJson = if (s.isSyntactic) pair("isSyntactic", s.isSyntactic) else null

    val branches: List[List[Int]] = if (s.branches == null) null else s.branches
      .map(branch => branch.map(n => n.id))
    val branchesJson = if (branches != null) pairDoubleList("branches", branches) else null

    val dataValueJson = if (s.data != null) render(s.data) else null
    val dataJson = if (dataValueJson != null) pairJsonObject("data", dataValueJson) else null

    val properties = List(idJson, labelJson, isJoinPointJson,
      isScopeOpenJson, isScopeCloseJson, isSyntacticJson, branchesJson, dataJson)
      .filterNot(jsonProperty => jsonProperty == null)

    "{" + properties.mkString(",") + "}"
  }

  def render(data: GenericNodeData): String = {
    val refIdJson = data.refId match {
      case Some(refId) => pair("refId", refId)
      case _ => null
    }
    val isSmtQueryJson = if (data.isSmtQuery) pair("isSmtQuery", data.isSmtQuery) else null
    val timeMsJson = data.timeMs match {
      case Some(timeMs) => pair("timeMs", timeMs)
      case _ => null
    }

    val properties = List(refIdJson, isSmtQueryJson, timeMsJson)
      .filterNot(jsonProperty => jsonProperty == null)

    if (properties.isEmpty) {
      null
    } else {
      "{" + properties.mkString(",") + "}"
    }
  }
}
