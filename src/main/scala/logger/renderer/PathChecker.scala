package viper.silicon.logger.renderer

import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data.DataRecord
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}

/**
  * Checks whether the given paths respect the following properties:
  * - each record has a unique id
  * - each open scope record is preceded by a data record
  * - each open scope record has a single close scope record
  * - scopes are either contained in each other or beside each other (but not overlapping)
  */
class PathChecker extends Renderer[MemberPath, String] {

  def render(memberList: List[MemberPath]): String = {
    var res = List[String]()
    for (m <- memberList) {
      res = res :+ renderMember(m)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderMember(s: MemberPath): String = {
    var res = List[String]()
    for (path <- s.paths) {
      res = res ++ renderPath(path)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderPath(path: List[SymbolicRecord]): List[String] = {
    var checks = List[String]()
    checks = checks ++ checkIdUniqueness(path)
    checks = checks ++ checkScopesExist(path)
    checks = checks ++ checkScopeNesting(path)
    checks
  }

  // checks: - each record has a unique id
  private def checkIdUniqueness(path: List[SymbolicRecord]): List[String] = {
    var checks = List[String]()
    var ids = List[Int]()

    for (record <- path) {
      if (ids.contains(record.id)) {
        checks = checks :+ "id " + record.id + " is not unique"
      } else {
        ids = ids :+ record.id
      }
    }

    checks
  }

  // checks: - each open scope record is preceded by a data record
  private def checkScopesExist(path: List[SymbolicRecord]): List[String] = {
    var checks = List[String]()

    for (index <- path.indices) {
      val currentRecord = path(index)
      val prevRecord = if (index - 1 >= 0) path(index - 1) else null

      currentRecord match {
        case os: OpenScopeRecord =>
          prevRecord match {
            case dr: DataRecord =>
              if (os.refId != dr.id) {
                checks = checks :+ "record " + dr.id + " is followed by a open scope record with invalid refId"
              }
            case _ =>
              checks = checks :+ "open scope record " + os.id + " has no preceeding data record"
          }
        case _ =>
      }
    }

    checks
  }

  // checks: - scopes are either contained in each other or beside each other (but not overlapping)
  // checks: - each open scope record has a single close scope record
  private def checkScopeNesting(path: List[SymbolicRecord]): List[String] = {
    var checks = List[String]()
    var scopeStack = List[OpenScopeRecord]()

    for (record <- path) {
      record match {
        case os: OpenScopeRecord => scopeStack = os :: scopeStack
        case cs: CloseScopeRecord =>
          val topScope = scopeStack.head
          if (topScope.refId != cs.refId) {
            checks = checks :+ "scope with refId " + cs.refId + " violates nesting (top refId" + topScope.refId + ")"
          } else {
            scopeStack = scopeStack.tail
          }
        case _ =>
      }
    }

    // the stack should be empty now
    scopeStack.foreach((os: OpenScopeRecord) => {
      checks = checks :+ "open scope " + os.id + " has no corresponding close scope record"
    })

    checks
  }
}
