// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package logger

import java.io.File
import java.nio.file.{Files, Path, Paths}

import logger.records.SymbolicRecord
import logger.records.data.{DataRecord, FunctionRecord, MethodRecord, PredicateRecord}
import logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import logger.records.structural.{BranchingRecord, JoiningRecord}
import logger.renderer.SimpleTreeRenderer
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.{Config, Map}
import viper.silver.ast
import viper.silver.verifier.AbstractError

import scala.annotation.elidable
import scala.annotation.elidable._

/* TODO: InsertionOrderedSet is used by the logger, but the insertion order is
 *       probably irrelevant for logging. I.e. it might be ok if these sets were
 *       traversed in non-deterministic order.
 */

/*
 *  For instructions on how to use/visualise recording, have a look at
 *  /utils/symbolicRecording/README_symbolicRecord.txt
 *
 * Overall concept:
 * 1) SymbExLogger Object:
 *    Is used as interface to access the logs. Code from this file that is used in Silicon
 *    should only be used via SymbExLogger. Contains a list of SymbLog, one SymbLog
 *    per method/function/predicate (member). The method 'currentLog()' gives access to the log
 *    of the currently executed member.
 * 2) SymbLog:
 *    Contains the log for a member. Most important methods: insert/collapse. To 'start'
 *    a record use insert, to finish the recording use collapse. There should be as many calls
 *    of collapse as of insert (theoretically; practically this is not possible due to branching.
 *    To avoid such cases, each insert gets an identifier, which is then used by collapse, to avoid
 *    multiple collapses per insert).
 * 3) Records:
 *    The basic abstract record type is SymbolicRecord. There is one record type for each of the
 *    four basic symbolic primitives evaluate, execute, consume and produce. For constructs of special
 *    interest (e.g., if-then-else-branching), there are separate records.
 *    The basic record looks conceptually as follows:
 *
 *    SymbolicRecord {
 *      subs = List[SymbolicRecord]
 *    }
 *
 *    Example to illustrate the way a silver program is logged:
 *    Assume the following silver code:
 *
 *    method m() {
 *      var a: Int
 *      a := 1
 *      a := a+2
 *    }
 *
 *    This results in a log that can be visualized as a
 *    simple tree (see: SimpleTreeRenderer) as follows:
 *
 *    method m
 *      execute a := 1
 *        evaluate 1
 *      execute a := a + 2
 *        evaluate a
 *        evaluate 2
 *
 *    The order of insert/collapse is as follows:
 *    insert(method), insert(execute), insert (evaluate),
 *    collapse(evaluate), collapse(execute),
 *    insert(execute), insert(evaluate) collapse(evaluate),
 *    insert(evaluate), collapse(evaluate)
 *    collapse(execute), collapse(method)
 *
 *    Collapse basically 'removes one indentation', i.e., brings you one level higher in the tree.
 *    For an overview of 'custom' records (e.g., for Branching, local branching, method calls etc.),
 *    have a look at the bottom of this file for a guide in how to create such records or take a look
 *    at already existing examples such as IfThenElseRecord, CondExpRecord or MethodCallRecord.
 */

object SymbExLogger {
  /** List of logged Method/Predicates/Functions. **/
  var memberList = List[SymbLog]()

  var enabled = false

  /** Config of Silicon. Used by StateFormatters. **/
  private var config: Config = _

  /** Add a new log for a method, function or predicate (member).
    *
    * @param member Either a MethodRecord, PredicateRecord or a FunctionRecord.
    * @param s      Current state. Since the body of the method (predicate/function) is not yet
    *               executed/logged, this is usually the empty state (use Σ(Ø, Ø, Ø) for empty
    *               state).
    * @param c      Current context.
    */
  @elidable(INFO)
  def insertMember(member: ast.Member, s: State, pcs: PathConditionStack) {
    memberList = memberList ++ List(new SymbLog(member, s, pcs))
  }

  /** Use this method to access the current log, e.g., to access the log of the method
    * that gets currently symbolically executed.
    *
    * @return Returns the current method, predicate or function that is being logged.
    */
  def currentLog(): SymbLog = {
    if (enabled)
      memberList.last
    else NoopSymbLog
  }

  def endMember(): Unit = {
    val closeRecord = new CloseScopeRecord(currentLog().main.id)
    currentLog().insert(closeRecord)
  }

  /**
    * Passes config from Silicon to SymbExLogger.
    * Config is assigned only once, further calls are ignored.
    *
    * @param c Config of Silicon.
    */
  def setConfig(c: Config) {
    if (config == null) {
      config = c
      // In both cases we need to record the trace
      setEnabled(config.ideModeAdvanced())
    }
  }

  @elidable(INFO)
  private def setEnabled(b: Boolean) {
    enabled = b
  }

  /** Gives back config from Silicon **/
  def getConfig(): Config = {
    config
  }

  /**
    * Simple string representation of the logs.
    */
  def toSimpleTreeString: String = {
    if (enabled) {
      val simpleTreeRenderer = new SimpleTreeRenderer()
      simpleTreeRenderer.render(memberList)
    } else ""
  }

  /**
    * Simple string representation of the logs, but contains only the types of the records
    * and not their values. Original purpose was usage for unit testing.
    */
  def toTypeTreeString(): String = {
    /*
    if (enabled) {
      val typeTreeRenderer = new TypeTreeRenderer()
      typeTreeRenderer.render(memberList)
    } else ""
     */
    ""
  }

  /**
    * Writes a .DOT-file with a representation of all logged methods, predicates, functions.
    * DOT-file can be interpreted with GraphViz (http://www.graphviz.org/)
    */
  @elidable(INFO)
  def writeDotFile() {
    /*
    if (config.writeTraceFile()) {
      val dotRenderer = new DotTreeRenderer()
      val str = dotRenderer.render(memberList)
      val pw = new java.io.PrintWriter(new File(getOutputFolder() + "dot_input.dot"))
      try pw.write(str) finally pw.close()
    }
     */
  }

  /**
    * Writes a .JS-file that can be used for representation of the logged methods, predicates
    * and functions in a HTML-file.
    */
  @elidable(INFO)
  def writeJSFile() {
    /*
    if (config.writeTraceFile()) {
      val pw = new java.io.PrintWriter(new File(getOutputFolder() + "executionTreeData.js"))
      try pw.write(toJSString()) finally pw.close()
    }
     */
  }

  /** A JSON representation of the log, used when sending back messages or when writing data to a
    * file.
    */
  /*
  @elidable(INFO)
  def toJSString(): String = new JSTreeRenderer().render(memberList)
  */
  protected def getOutputFolder(): String = {
    ""
  }

  /** Path to the file that is being executed. Is used for UnitTesting. **/
  var filePath: Path = null

  /** Unit Testing **/
  var unitTestEngine: SymbExLogUnitTest = null

  /** Initialize Unit Testing. Should be done AFTER the file to be tested is known. **/
  def initUnitTestEngine() {
    if (filePath != null)
      unitTestEngine = new SymbExLogUnitTest(filePath)
  }

  /**
    * Resets the SymbExLogger-object, to make it ready for a new file.
    * Only needed when several files are verified together (e.g., sbt test).
    */
  def reset() {
    memberList = List[SymbLog]()
    unitTestEngine = null
    filePath = null
    config = null
  }

  def resetMemberList() {
    memberList = List[SymbLog]()
  }

  def checkMemberList(): String = {
    /*
    new ExecTimeChecker().render(memberList)
     */
    ""
  }

  /**
    * Converts memberList to a tree of GenericNodes
    */
  def convertMemberList(): GenericNode = {
    /*
    new GenericNodeRenderer().render(memberList)
    */
    null
  }

  def writeChromeTraceFile(genericNode: GenericNode): Unit = {
    /*
    if (config.writeTraceFile()) {
      val chromeTraceRenderer = new ChromeTraceRenderer()
      val str = chromeTraceRenderer.render(List(genericNode))
      val pw = new java.io.PrintWriter(new File(getOutputFolder() + "chromeTrace.json"))
      try pw.write(str) finally pw.close()
    }
     */
  }

  def writeGenericNodeJsonFile(genericNode: GenericNode): Unit = {
    /*
    if (config.writeTraceFile()) {
      val jsonRenderer = new JsonRenderer()
      val str = jsonRenderer.render(List(genericNode))
      val pw = new java.io.PrintWriter(new File(getOutputFolder() + "genericNodes.json"))
      try pw.write(str) finally pw.close()
    }
     */
  }
}

//========================= SymbLog ========================

/**
  * Concept: One object of SymbLog per Method/Predicate/Function. SymbLog
  * is used in the SymbExLogger-object.
  */
class SymbLog(v: ast.Member, s: State, pcs: PathConditionStack) {

  var log = List[SymbolicRecord]()
  var branchingStack = List[BranchingRecord]()

  // Maps macros to their body
  private var _macros = Map[App, Term]()
  private var uidCounter = 0

  var main = v match {
    case m: ast.Method => new MethodRecord(m, s, pcs)
    case p: ast.Predicate => new PredicateRecord(p, s, pcs)
    case f: ast.Function => new FunctionRecord(f, s, pcs)
    case default => null
  }
  insert(main)

  private def freshUid(): Int = {
    val uid = uidCounter
    uidCounter = uidCounter + 1
    uid
  }

  private def appendLog(r: SymbolicRecord): Unit = {
    if (branchingStack.isEmpty) {
      log = log :+ r
    } else {
      branchingStack.head.appendLog(r)
    }
  }

  @elidable(INFO)
  def insert(s: DataRecord): Int = {
    s.id = freshUid()
    appendLog(s)
    val openRecord = new OpenScopeRecord(s)
    insert(openRecord)
    s.id
  }

  @elidable(INFO)
  def insert(s: ScopingRecord): Int = {
    s.id = freshUid()
    appendLog(s)
    s.id
  }

  @elidable(INFO)
  def insertBranchPoint(ref: DataRecord): Int = {
    val branchingRecord = new BranchingRecord(ref)
    branchingRecord.id = freshUid()
    appendLog(branchingRecord)
    branchingStack = branchingRecord :: branchingStack
    branchingRecord.id
  }

  @elidable(INFO)
  def switchToNextBranch(uidBranchPoint: Int): Unit = {
    // TODO get correct branch in case of enclosed branches
    assert(branchingStack.nonEmpty)
    // close current branch:
    val closeRecord = new CloseScopeRecord(uidBranchPoint)
    insert(closeRecord)
    val branchingRecord = branchingStack.head
    branchingRecord.switchToNextBranch()
  }

  @elidable(INFO)
  def insertJoinPoint(): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    collapseBranchPoint(branchingRecord.id)
    val joiningRecord = new JoiningRecord(branchingRecord)
    joiningRecord.id = freshUid()
    appendLog(joiningRecord)
  }

  // TODO legacy
  @elidable(INFO)
  def collapse(v: ast.Node, n: Int): Unit = {
    val closeRecord = new CloseScopeRecord(n)
    insert(closeRecord)
  }

  /**
    * Only necessary in case no joining (i.e. call to insertJoinPoint) occurs
    * @param uidBranchPoint
    */
  @elidable(INFO)
  // TODO legacy
  def collapseBranchPoint(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    val closeRecord = new CloseScopeRecord(uidBranchPoint)
    insert(closeRecord)
    branchingStack = branchingStack.tail
  }

  /** Record the last prover query that failed.
    *
    * This is used to record failed SMT queries, that ultimately led Silicon
    * to a verification failure. Whenever a new SMT query is successful, then
    * the currently recorded one is supposed to be discarded (via the
    * discardSMTQuery method), because it did not cause a failure.
    *
    * @param query The query to be recorded.
    */
  @elidable(INFO)
  def setSMTQuery(query: Term): Unit = {
    if (main != null) {
      main.lastFailedProverQuery = Some(query)
    }
  }

  /** Discard the currently recorded SMT query.
    *
    * This is supposed to be called when we know the recorded SMT query cannot
    * have been the reason for a verification failure (e.g. a new query has
    * been performed afterwards).
    */
  @elidable(INFO)
  def discardSMTQuery(): Unit = {
    if (main != null) {
      main.lastFailedProverQuery = None
    }
  }

  def macros() = _macros

  @elidable(INFO)
  def addMacro(m: App, body: Term): Unit = {
    _macros = _macros + (m -> body)
  }

  override def toString: String = new SimpleTreeRenderer().renderMember(this)
}

object NoopSymbLog extends SymbLog(null, null, null) {
  override def insert(s: DataRecord): Int = 0
  override def insert(s: ScopingRecord): Int = 0
  override def insertBranchPoint(ref: DataRecord): Int = 0
  override def switchToNextBranch(uidBranchPoint: Int): Unit = {}
  override def insertJoinPoint(): Unit = {}
  override def collapse(v: ast.Node, n: Int): Unit = {}
}

//===== Renderer Classes =====
/*

class DotTreeRenderer extends Renderer[SymbLog, String] {

  def render(memberList: List[SymbLog]): String = {
    var str: String = "digraph {\n"
    str = str + "node [shape=rectangle];\n\n"

    for (m <- memberList) {
      str = str + renderMember(m) + "\n\n"
    }

    str = str + "}"
    str
  }

  def renderMember(s: SymbLog): String = {
    val main = s.main
    var output = ""

    output += "    " + main.dotNode() + " [label=" + main.dotLabel() + "];\n"
    output += subsToDot(main)
    output
  }

  private var previousNode = ""
  private var unique_node_nr = this.hashCode()

  private def unique_node_number(): Int = {
    unique_node_nr = unique_node_nr + 1
    unique_node_nr
  }

  private def subsToDot(s: SymbolicRecord): String = {
    previousNode = s.dotNode()

    var output = ""

    s match {
      case imp: GlobalBranchRecord => {
        val imp_parent = previousNode
        for (rec <- imp.thnSubs) {
          output += "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output += "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output += subsToDot(rec)
        }
        previousNode = imp_parent
        for (rec <- imp.elsSubs) {
          output += "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output += "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output += subsToDot(rec)
        }
      }

      case mc: MethodCallRecord => {
        val mc_parent = previousNode
        output += "    " + mc.dotNode() + " [label=" + mc.dotLabel() + "];\n"
        previousNode = mc.dotNode()

        for (p <- mc.parameters) {
          output += "    " + p.dotNode() + " [label=\"parameter: " + p.toSimpleString() + "\"];\n"
          output += "    " + previousNode + " -> " + p.dotNode() + ";\n"
          output += subsToDot(p)
        }
        previousNode = mc.dotNode()

        for (p <- mc.precondition) {
          output += "    " + p.dotNode() + " [label=\"precondition: " + p.toSimpleString() + "\"];\n"
          output += "    " + previousNode + " -> " + p.dotNode() + ";\n"
          output += subsToDot(p)
        }
        previousNode = mc.dotNode()

        for (p <- mc.postcondition) {
          output += "    " + p.dotNode() + " [label=\"postcondition: " + p.toSimpleString() + "\"];\n"
          output += "    " + previousNode + " -> " + p.dotNode() + ";\n"
          output += subsToDot(p)
        }
        previousNode = mc.dotNode()


      }
      case _ => {
        if (s.subs.isEmpty)
          return ""
        for (rec <- s.subs) {
          output += "    " + rec.dotNode() + " [label=" + rec.dotLabel() + "];\n"
          output += "    " + previousNode + " -> " + rec.dotNode() + ";\n"
          output += subsToDot(rec)
        }
      }
    }
    output
  }
}

object JsonHelper {
  def pair(name: String, value: String): String = {
    "\"" + name + "\": " + "\"" + escape(value) + "\""
  }

  def pair(name: String, value: Boolean): String = {
    "\"" + name + "\":" + value
  }

  def pair(name: String, value: Long): String = {
    "\"" + name + "\":" + value
  }

  def pair(name: String, value: List[Int]): String = {
    "\"" + name + "\":[" + value.mkString(",") + "]"
  }

  def escape(s: String): String = {
    var res = s
    var i = 0
    while (i < res.length()) {
      if (res(i).equals('\n')) {
        res = res.substring(0, i - 1) + "\\n" + res.substring(i + 1, res.length())
        i += 1
      } else if (res(i).equals('\\')) {
        res = res.substring(0, i - 1) + "\\\\" + res.substring(i + 1, res.length())
        i += 1
      }
      i += 1
    }
    res
  }
}

class JSTreeRenderer extends Renderer[SymbLog, String] {

  val stateFormatter: DefaultStateFormatter
  = new DefaultStateFormatter()

  def render(memberList: List[SymbLog]): String = {
    "var executionTreeData = [\n" + memberList.map(s => renderMember(s)).fold("") { (a, b) => if (a.isEmpty) b else a + ", \n" + b } + "]\n"
  }

  def renderMember(member: SymbLog): String = {
    recordToJS(member.main) + "\n"
  }

  private def recordToJS(s: SymbolicRecord): String = {
    var output = ""
    val kind = "kind"
    val children = "\"children\""
    val open = JsonHelper.pair("open", true)

    s match {
      case gb: GlobalBranchRecord => {
        output += "{" + gb.toJson() + "," + open + printState(gb)
        output += "\n," + children + ": [\n"
        output += "{" + JsonHelper.pair(kind, "Branch 1") + "," + open
        output += ",\n" + children + ": [\n"
        output += combine(gb.thnSubs)
        output += "]},\n"
        output += "{" + JsonHelper.pair(kind, "Branch 2") + "," + open
        output += ",\n" + children + ": [\n"
        output += combine(gb.elsSubs)
        output += "]}\n"
        output += "]}"
      }
      case mc: MethodCallRecord => {
        output += "{" + mc.toJson() + "," + open + printState(mc)
        output += "\n," + children + ": [\n"

        output += "{" + JsonHelper.pair(kind, "parameters") + "," + open
        output += "\n," + children + ": [\n"
        output += combine(mc.parameters)
        output += "]},"

        output += "{" + JsonHelper.pair(kind, "precondition") + "," + open + printState(mc.precondition(0))
        output += "\n," + children + ": [\n"
        output += combine(mc.precondition)
        output += "]},"

        output += "{" + JsonHelper.pair(kind, "postcondition") + "," + open + printState(mc.postcondition(0))
        output += "\n," + children + ": [\n"
        output += combine(mc.postcondition)
        output += "]}"

        output += "]}"
      }
      case cr: CommentRecord => {
        output += "{" + JsonHelper.pair(kind, "comment") + "," + cr.toJson() + "," + open + "}"
      }
      case _ => {
        var innerValue = s.toJson()
        if(innerValue != ""){
          innerValue += ","
        }
        output += "{" + innerValue + open + printState(s)
        if (s.subs.nonEmpty) {
          output += ",\n" + children + ": [\n"
          output += combine(s.subs)
          output += "]"
        }
        output += "}"
      }
    }
    output
  }

  def combine(list: List[SymbolicRecord]): String = {
    list.map(s => recordToJS(s)).fold("") { (a, b) => if (a.isEmpty) b else a + ",\n" + b } + "\n"
  }

  def printState(s: SymbolicRecord): String = {
    var res = ""
    if (s.state != null) {
      var σ = s.state.asInstanceOf[State]
      res = ",\"prestate\":" + JsonHelper.escape(stateFormatter.toJson(σ, s.pcs))
    }
    res
  }
}

class ExecTimeChecker extends Renderer[SymbLog, String] {
  def render(memberList: List[SymbLog]): String = {
    var res = List[String]()
    for (m <- memberList) {
      res = res :+ renderMember(m)
    }
    res.filter(check => check != "")
      .mkString("\n")
  }

  def renderMember(member: SymbLog): String = {
    checkRecord(member.main)
  }

  def checkRecord(s: SymbolicRecord): String = {
    var checks = getSubs(s)
      .map(checkRecord)
      .filter(check => check != "")
    // ignore unreachable records:
    var ignore = false
    s match {
      case cr: CommentRecord =>
        if (cr.comment.equals("Unreachable")) {
          ignore = true
        }
      case _ =>
    }
    if (!ignore &&
      (s.startTimeMs == 0
      || s.endTimeMs == 0)) {
      checks = checks :+ "incomplete exec timing: " + s.toString()
    }
    checks.mkString("\n")
  }

  def getSubs(s: SymbolicRecord): List[SymbolicRecord] = {
    s match {
      case ce: ConditionalEdgeRecord =>
        ce.subs ++ ce.cond ++ ce.thnSubs
      case gb: GlobalBranchRecord =>
        gb.subs ++ gb.cond ++ gb.thnSubs ++ gb.elsSubs
      case lb: LocalBranchRecord =>
        lb.subs ++ lb.cond ++ lb.thnSubs ++ lb.elsSubs
      case mc: MethodCallRecord =>
        mc.subs ++ mc.precondition ++ mc.postcondition ++ mc.parameters
      case _ => s.subs
    }
  }
}

class TypeTreeRenderer extends Renderer[SymbLog, String] {
  def render(memberList: List[SymbLog]): String = {
    var res = ""
    for (m <- memberList) {
      res = res + renderMember(m) + "\n"
    }
    res
  }

  def renderMember(member: SymbLog): String = {
    toTypeTree(member.main, 1)
  }

  def toTypeTree(s: SymbolicRecord, n: Int): String = {
    var indent = ""
    for (i <- 1 to n) {
      indent = "  " + indent
    }
    var str = ""

    s match {
      case gb: GlobalBranchRecord => {
        str = str + gb.toTypeString + "\n"
        for (sub <- gb.thnSubs) {
          str = str + indent + toTypeTree(sub, n + 1)
        }
        for (sub <- gb.elsSubs) {
          str = str + indent + toTypeTree(sub, n + 1)
        }
      }
      case mc: MethodCallRecord => {
        str = str + "MethodCall\n"
        for (p <- mc.precondition) {
          str = str + indent + "precondition\n"
          str = str + indent + "  " + toTypeTree(p, n + 2)
        }
        for (p <- mc.postcondition) {
          str = str + indent + "postcondition\n"
          str = str + indent + "  " + toTypeTree(p, n + 2)
        }
        for (p <- mc.parameters) {
          str = str + indent + "parameter\n"
          str = str + indent + "  " + toTypeTree(p, n + 2)
        }
      }
      case _ => {
        str = s.toTypeString() + "\n"
        for (sub <- s.subs) {
          str = str + indent + toTypeTree(sub, n + 1)
        }
      }
    }
    str
  }
}
*/

//=========== Records =========
/*
sealed trait SymbolicRecord {

  def toJson(): String = {
    if (value != null) JsonHelper.pair("value", value.toString())
    else ""
  }

  def dotNode(): String = {
    this.hashCode().toString()
  }

  def dotLabel(): String = {
    "\"" + this.toString() + "\""
  }
}

class MethodRecord(v: ast.Method, s: State, p: PathConditionStack) extends MemberRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", "Method") + "," + JsonHelper.pair("value", value.name)
    else ""
  }
}

class PredicateRecord(v: ast.Predicate, s: State, p: PathConditionStack) extends MemberRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", "Predicate") + "," + JsonHelper.pair("value", value.name)
    else ""
  }
}

class FunctionRecord(v: ast.Function, s: State, p: PathConditionStack) extends MemberRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", "Function") + "," + JsonHelper.pair("value", value.name)
    else ""
  }
}

class ExecuteRecord(v: ast.Stmt, s: State, p: PathConditionStack) extends SequentialRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("type", "execute") + "," + JsonHelper.pair("pos", utils.ast.sourceLineColumn(value)) + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class EvaluateRecord(v: ast.Exp, s: State, p: PathConditionStack) extends SequentialRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("type", "evaluate") + "," + JsonHelper.pair("pos", utils.ast.sourceLineColumn(value)) + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class ProduceRecord(v: ast.Exp, s: State, p: PathConditionStack) extends SequentialRecord {
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("type", "produce") + "," + JsonHelper.pair("pos", utils.ast.sourceLineColumn(value)) + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class ConsumeRecord(v: ast.Exp, s: State, p: PathConditionStack)
  override def toJson(): String = {
    if (value != null) JsonHelper.pair("type", "consume") + "," + JsonHelper.pair("pos", utils.ast.sourceLineColumn(value)) + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class WellformednessCheckRecord(v: Seq[ast.Exp], s: State, p: PathConditionStack)
  override def toJson(): String = {
    JsonHelper.pair("kind", "WellformednessCheck")
  }
}

abstract class TwoBranchRecord(v: ast.Exp, s: State, p: PathConditionStack, env: String)
  extends MultiChildUnorderedRecord {

  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", toTypeString()) + "," + JsonHelper.pair("value", value.toString())
    else ""
  }

  override def toString(): String = {
    environment + " " + toSimpleString()
  }
}

class CfgBranchRecord(v: Seq[SilverEdge], s: State, p: PathConditionStack, env: String)
  extends MultiChildUnorderedRecord {

  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", "CfgBranch") + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class ConditionalEdgeRecord(v: ast.Exp, s: State, p: PathConditionStack, env: String)
  extends MultiChildUnorderedRecord {

  override def toJson(): String = {
    if (value != null) JsonHelper.pair("kind", "ConditionalEdge") + "," + JsonHelper.pair("value", value.toString())
    else ""
  }
}

class CommentRecord(str: String, s: State, p: PathConditionStack) extends SequentialRecord {

  override def toJson(): String = {
    if (comment != null) JsonHelper.pair("value", comment)
    else ""
  }

  override def dotLabel(): String = {
    "\"" + comment + "\""
  }
}

class MethodCallRecord(v: ast.MethodCall, s: State, p: PathConditionStack)
  extends MultiChildOrderedRecord {

  override def toString(): String = {
    if (value != null)
      "execute: " + value.toString()
    else
      "execute: MethodCall <null>"
  }

  override def toJson(): String = {
    if (v != null) JsonHelper.pair("kind", "MethodCall") + "," + JsonHelper.pair("value", v.toString())
    else ""
  }
}

class SingleMergeRecord(val destChunks: Seq[NonQuantifiedChunk], val newChunks: Seq[NonQuantifiedChunk],
                        p: PathConditionStack) extends MemberRecord {
  val value: ast.Node = null
  val state: State = null
  val pcs = if (p != null) p.assumptions else null

  def toTypeString(): String = {
    "SingleMerge"
  }

  override def toString(): String = {
    if (destChunks != null && newChunks != null) {
      val newChunksString = newChunks.mkString(" ")
      if (newChunksString == "") {
        "Single merge: " + destChunks.mkString(" ") + " <="
      } else {
        "Single merge: " + destChunks.mkString(" ") + " <= " + newChunksString
      }
    } else {
      "Single merge: <null>"
    }
  }
}
*/

class GenericNode(val label: String) {

  // ==== structural
  var children = List[GenericNode]()
  var successors = List[GenericNode]()
  // ==== structural

  var isSyntactic: Boolean = false
  var isSmtQuery: Boolean = false
  var startTimeMs: Long = 0
  var endTimeMs: Long = 0

  override def toString(): String = {
    label
  }
}
/*
class GenericNodeRenderer extends Renderer[SymbLog, GenericNode] {

  def render(memberList: List[SymbLog]): GenericNode = {
    var children: List[GenericNode] = List()
    for (m <- memberList) {
      children = children ++ List(renderMember(m))
    }
    var startTimeMs: Long = 0
    var endTimeMs: Long = 0
    for (m <- memberList) {
      if (m.main != null) {
        if (startTimeMs == 0 || m.main.startTimeMs < startTimeMs) {
          startTimeMs = m.main.startTimeMs
        }
        if (m.main.endTimeMs > endTimeMs) {
          endTimeMs = m.main.endTimeMs
        }
      }
    }
    val node = new GenericNode("Members")
    node.startTimeMs = startTimeMs
    node.endTimeMs = endTimeMs
    node.children = children
    node
  }

  def renderMember(s: SymbLog): GenericNode = {
    /*
    // adjust start and end time of s.main:
    // TODO this should not be necessary!
    if (s.main.subs.nonEmpty) {
      s.main.startTimeMs = s.main.subs.head.startTimeMs
      s.main.endTimeMs = s.main.subs.last.endTimeMs
    }
    */
    renderRecord(s.main)
  }

  def renderRecord(r: SymbolicRecord): GenericNode = {

    var node = new GenericNode(r.toString())
    node.startTimeMs = r.startTimeMs
    node.endTimeMs = r.endTimeMs
    // set isSmtQuery flag:
    r match {
      case sq: ProverAssertRecord => node.isSmtQuery = true
      case _ =>
    }

    // TODO replace CondExpr with corresponding Branch and Join records
    r match {
      case cbRecord: CfgBranchRecord => {
        // branches are successors
        for (branchSubs <- cbRecord.branchSubs) {
          if (branchSubs.length != 1) {
            throw new AssertionError("each branch should only have one sub which should be a ConditionalEdgeRecord")
          }
          val branchNode = renderRecord(branchSubs.head)
          node.successors = node.successors ++ List(branchNode)
        }
        node.isSyntactic = true
        // end time corresponds to the start time of the first branch
        for (successor <- node.successors) {
          if (successor.startTimeMs < node.endTimeMs) {
            node.endTimeMs = successor.startTimeMs
          }
        }
      }

      case ceRecord: ConditionalEdgeRecord => {
        // insert condition as child
        node.children = node.children ++ (ceRecord.cond map renderRecord)
        // the end time corresponds to the end time of the condition:
        node.endTimeMs = ceRecord.condEndTimeMs
        // stmts of the basic blocks (following the condition) are attached as a single branch node to the successors
        val branchNode = renderBranch(ceRecord.thnSubs, ceRecord.condEndTimeMs, ceRecord.thnEndTimeMs)
        node.successors = node.successors ++ List(branchNode)
      }

      case ueRecord: UnconditionalEdgeRecord => {
        node.isSyntactic = true
        node.children = node.children ++ (r.subs map renderRecord)
      }

      case gb: GlobalBranchRecord => {
        // insert condition as child
        node.children = node.children ++ (gb.cond map renderRecord)
        // the end time corresponds to the end time of the condition:
        node.endTimeMs = gb.condEndTimeMs
        // if and else branch are two successors
        val thnNode = renderBranch(gb.thnSubs, gb.condEndTimeMs, gb.thnEndTimeMs)
        val elsNode = renderBranch(gb.elsSubs, gb.thnEndTimeMs, gb.elsEndTimeMs)
        node.successors = node.successors ++ List(thnNode, elsNode)
      }

      case lb: LocalBranchRecord => {
        // node is the branch node having then and else nodes as successors.
        // then and else nodes have themselves the join node as successor
        node.children = node.children ++ (lb.cond map renderRecord)
        // the end time corresponds to the end time of the condition:
        node.endTimeMs = lb.condEndTimeMs
        // if and else branch are two successors
        val thnNode = renderBranch(lb.thnSubs, lb.condEndTimeMs, lb.thnEndTimeMs)
        val elsNode = renderBranch(lb.elsSubs, lb.thnEndTimeMs, lb.elsEndTimeMs)
        node.successors = node.successors ++ List(thnNode, elsNode)
        // assign same node as successor of thnNode and elsNode:
        var joinNode = new GenericNode("Join Point")
        // TODO get join duration
        joinNode.startTimeMs = lb.elsEndTimeMs
        joinNode.endTimeMs = lb.endTimeMs
        thnNode.successors = thnNode.successors ++ List(joinNode)
        elsNode.successors = elsNode.successors ++ List(joinNode)
      }

      case _ => {
        node.children = node.children ++ (r.subs map renderRecord)
      }
    }

    node
  }

  def renderBranch(branchSubs: List[SymbolicRecord], branchStartTimeMs: Long, branchEndTimeMs: Long): GenericNode = {
    val branchNode = new GenericNode("Branch")
    branchNode.startTimeMs = branchStartTimeMs
    branchNode.endTimeMs = branchEndTimeMs
    branchNode.isSyntactic = true
    for (sub <- branchSubs) {
      branchNode.children = branchNode.children ++ List(renderRecord(sub))
    }
    branchNode
  }
}

class ChromeTraceRenderer extends Renderer[GenericNode, String] {

  def render(memberList: List[GenericNode]): String = {
    val renderedMembers: Iterable[String] = memberList map renderMember
    "[" + renderedMembers.mkString(",") + "]"
  }

  // creates an event json object for each node
  // {"name": "Asub", "cat": "PERF", "ph": "B", "pid": 22630, "tid": 22630, "ts": 829}
  def renderMember(n: GenericNode): String = {
    val renderedChildren = (n.children map renderMember) filter(p => p != null && p!= "")
    val renderedSuccessors = (n.successors map renderMember) filter(p => p != null && p!= "")
    val renderedNode = renderNode(n)
    if (renderedNode == null) {
      println("skipping node " + n.toString())
      return ""
    }
    (List(renderedNode) ++ renderedChildren ++ renderedSuccessors).mkString(",")
  }

  // renders a node without considering its children or successors
  def renderNode(n: GenericNode): String = {
    if (n.startTimeMs == 0 || n.endTimeMs == 0) {
      return null
    }
    // start event
    "{" + JsonHelper.pair("name", n.label) + "," +
      JsonHelper.pair("cat", "PERF") + "," +
      JsonHelper.pair("ph", "B") + "," +
      JsonHelper.pair("pid", 1) + "," +
      JsonHelper.pair("tid", 1) + "," +
      JsonHelper.pair("ts", n.startTimeMs) + "}," +
    // end event
      "{" + JsonHelper.pair("name", n.label) + "," +
      JsonHelper.pair("cat", "PERF") + "," +
      JsonHelper.pair("ph", "E") + "," +
      JsonHelper.pair("pid", 1) + "," +
      JsonHelper.pair("tid", 1) + "," +
      JsonHelper.pair("ts", n.endTimeMs) + "}"
  }
}

class JsonRenderer extends Renderer[GenericNode, String] {
  // visit all nodes and insert them into an array such that each node can be referenced by its index
  var nodes: List[GenericNode] = List()

  override def render(memberList: List[GenericNode]): String = {
    memberList foreach buildHierarchy

    val renderedMembers: Iterable[String] = nodes map renderMember
    "[" + renderedMembers.mkString(",") + "]"
  }

  def buildHierarchy(n: GenericNode): Unit = {
    // add node to list of all nodes:
    if (!nodes.contains(n)) {
      nodes = nodes ++ List(n)
    }

    n.children foreach buildHierarchy
    n.successors foreach buildHierarchy
  }

  override def renderMember(n: GenericNode): String = {
    val childrenIndices = n.children map nodes.indexOf
    val successorsIndices = n.successors map nodes.indexOf
    if (childrenIndices.contains(-1) || successorsIndices.contains(-1)) {
      println("unresolved node found; skipping node " + n.toString())
      return "{" + JsonHelper.pair("label", n.label) + "}"
    }
    "{" + JsonHelper.pair("id", nodes.indexOf(n)) + "," +
      JsonHelper.pair("label", n.label) + "," +
      JsonHelper.pair("isSmtQuery", n.isSmtQuery) + "," +
      JsonHelper.pair("isSyntactic", n.isSyntactic) + "," +
      JsonHelper.pair("startTimeMs", n.startTimeMs) + "," +
      JsonHelper.pair("endTimeMs", n.endTimeMs) + "," +
      JsonHelper.pair("children", childrenIndices) + "," +
      JsonHelper.pair("successors", successorsIndices) + "}"
  }
}
*/

/**
  * ================================
  * GUIDE FOR ADDING RECORDS TO SymbExLogger
  * ================================
  *
  * SymbExLogger records all calls of the four symbolic primitives Execute, Evaluate, Produce
  * and Consume. By default, only the current state, context and parameters of the primitives are stored.
  * If you want to get more information from certain structures, there are several ways to store additional
  * info:
  *
  * 1) Store the information as a CommentRecord.
  * 2) Implement a customized record.
  *
  * Use of CommentRecord (1):
  * At the point in the code where you want to add the comment, call
  * //SymbExLogger.currentLog().insert(new CommentRecord(my_info, σ, c)
  * //SymbExLogger.currentLog().collapse()
  * σ is the current state (AnyRef, but should be of type State[_,_,_] usually), my_info
  * is a string that contains the information you want to store, c is the current
  * context. If you want to store more information than just a string, consider (2).
  *
  * Use of custom Records (2):
  * For already existing examples, have a look at CondExpRecord (local Branching) or IfThenElseRecord
  * (recording of If-Then-Else-structures).
  * Assume that you want to have a custom record for  (non-short-circuiting) evaluations of
  * ast.And, since you want to differ between the evaluation of the lefthandside
  * and the righthandside (not possible with default recording).
  * Your custom record could look similar to this:
  *
  * class AndRecord(v: ast.And, s: AnyRef, c: DefaultContext) extends SymbolicRecord {
  * val value = v    // Due to inheritance. This is what gets recorded by default.
  * val state = s    // "
  * val context = c  // "
  *
  * lhs: SymbolicRecord = new CommentRecord("null", null, null)
  * rhs: SymbolicRecord = new CommentRecord("null", null, null)
  * // lhs & rhs are what you're interested in. The first initialization should be overwritten anyway,
  * // initialization with a CommentRecord just ensures that the logger won't crash due
  * // to a Null Exception (ideally). Can also be used if you're unsure if a certain structure is
  * // evaluated at all; e.g., the righthandside might not be evaluated because the lefthandside
  * // is already false (see IfThenElseRecord: paths might be unreachable, so the default is
  * // a CommentRecord("Unreachable", null, null) which is not overwritten due to unreachability.
  *
  * def finish_lhs(): Unit = {
  * if(!subs.isEmpty) //so you don't overwrite your default CommentRecord if subs is empty
  * lhs = subs(0)
  * subs = List[SymbolicRecord]()
  * }
  *
  * def finish_rhs(): Unit = {
  * if(!subs.isEmpty)
  * rhs = subs(0)
  * subs = List[SymbolicRecord]()
  * }
  *
  * // finish_FIELD() is the method that overwrites the given field with what is currently in 'subs'.
  * // For usage example, see below.
  * }
  *
  * Usage of your new custom record 'AndRecord':
  * This is the code in the DefaultEvaluator (after unrolling of evalBinOp):
  *
  * case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
  * eval(σ, e0, pve, c)((t0, c1) =>
  * eval(σ, e1, pve, c1)((t1, c2) =>
  * Q(And(t0, t1), c2)))
  *
  * Use of the new record:
  *
  * case and @ ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
  * andRec = new AndRecord(and, σ, c)
  * SymbExLogger.currentLog().insert(andRec)
  * eval(σ, e0, pve, c)((t0, c1) => {
  * andRec.finish_lhs()
  * eval(σ, e1, pve, c1)((t1, c2) => {
  * andRec.finish_rhs()
  * SymbExLogger.currentLog().collapse()
  * Q(And(t0, t1), c2)))}}
  *
  * The record is now available for use; now its representation needs to be implemented,
  * which is done Renderer-Classes. Implement a new case in all renderer for the new
  * record.
  */

class SymbExLogUnitTest(f: Path) {
  private val originalFilePath: Path = f
  private val fileName: Path = originalFilePath.getFileName()

  /**
    * If there is a predefined 'expected-output'-file (.elog) for the currently verified program,
    * a 'actual output'-file is created (.alog) and then compared with the expected output. Should
    * only be called if the whole verification process is already terminated.
    */
  def verify(): Seq[SymbExLogUnitTestError] = {
    val expectedPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".elog").toString()
    val actualPath = Paths.get("src/test/resources/symbExLogTests/" + fileName + ".alog").toString()
    var errorMsg = ""
    var testFailed = false
    val testIsExecuted = Files.exists(Paths.get(expectedPath))

    if (testIsExecuted) {
      val pw = new java.io.PrintWriter(new File(actualPath))
      try pw.write(SymbExLogger.toSimpleTreeString) finally pw.close()

      val expectedSource = scala.io.Source.fromFile(expectedPath)
      val expected = expectedSource.getLines()

      val actualSource = scala.io.Source.fromFile(actualPath)
      val actual = actualSource.getLines()

      var lineNumber = 0

      while (!testFailed && expected.hasNext && actual.hasNext) {
        if (!actual.next().equals(expected.next())) {
          testFailed = true
        }
        lineNumber = lineNumber + 1
      }
      if (actual.hasNext != expected.hasNext)
        testFailed = true

      if (testFailed) {
        errorMsg = errorMsg + "Unit Test failed, expected output "
        errorMsg = errorMsg + "does not match actual output. "
        errorMsg = errorMsg + "First occurrence at line " + lineNumber + ".\n"
        errorMsg = errorMsg + "Compared Files:\n"
        errorMsg = errorMsg + "expected: " + expectedPath.toString() + "\n"
        errorMsg = errorMsg + "actual:   " + actualPath.toString() + "\n"
      }

      val execTimeOutput = SymbExLogger.checkMemberList()
      if (execTimeOutput != "") {
        testFailed = true
        errorMsg = errorMsg + "ExecTimeChecker: " + execTimeOutput + "\n"
      }

      actualSource.close()
      expectedSource.close()
    }
    if (testIsExecuted && testFailed) {
      Seq(new SymbExLogUnitTestError(errorMsg))
    }
    else {
      Nil
    }
  }
}

case class SymbExLogUnitTestError(msg: String) extends AbstractError {
  def pos = ast.NoPosition

  def fullId = "symbexlogunittest.error"

  def readableMessage = msg
}
