// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger

import java.nio.file.Path

import logger.renderer.StructuralTreeRenderer
import viper.silicon.decider.PathConditionStack
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data.{DataRecord, FunctionRecord, MethodRecord, PredicateRecord}
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.logger.renderer.SimpleTreeRenderer
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.{Config, Map}
import viper.silver.ast

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
  private var uidCounter = 0

  var enabled = false

  /** Config of Silicon. Used by StateFormatters. **/
  private var config: Config = _

  def freshUid(): Int = {
    val uid = uidCounter
    uidCounter = uidCounter + 1
    uid
  }

  /**
    * stores the last SMT solver statistics to calculate the diff
    */
  private var prevSmtStatistics: Map[String, String] = new Map()

  /** Add a new log for a method, function or predicate (member).
    *
    * @param member Either a MethodRecord, PredicateRecord or a FunctionRecord.
    * @param s      Current state. Since the body of the method (predicate/function) is not yet
    *               executed/logged, this is usually the empty state (use Σ(Ø, Ø, Ø) for empty
    *               state).
    * @param pcs    Current path conditions.
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
    * Converts the recorded log to a representation which only contains MemberRecords and structural records.
    * The intention of this representation is to ensure some form of robustness for unit test, because it is not
    * affected by removal or addition of (other) data or scope nodes
    */
  def toStructuralTreeString(): String = {
    if (enabled) {
      val structuralTreeRenderer = new StructuralTreeRenderer()
      structuralTreeRenderer.render(memberList)
    } else ""
  }

  /** Path to the file that is being executed. Is used for UnitTesting. **/
  var filePath: Path = null

  /**
    * Resets the SymbExLogger-object, to make it ready for a new file.
    * Only needed when several files are verified together (e.g., sbt test).
    */
  def reset() {
    memberList = List[SymbLog]()
    uidCounter = 0
    filePath = null
    config = null
  }

  def resetMemberList() {
    memberList = List[SymbLog]()
  }

  /**
    * Calculates diff between `currentStatistics` and the statistics from a previous call.
    * The difference is calculated if value can be converted to an int or double
    * @param currentStatistics most recent statistics from the SMT solver
    * @return map with differences (only containing values that could be converted) and keys with appended "-delta"
    */
  def getDeltaSmtStatistics(currentStatistics: Map[String, String]) : Map[String, String] = {
    val deltaStatistics = (currentStatistics map getDelta filter { case (_, value) => value.nonEmpty } map {
      case (key, Some(value)) => (key + "-delta", value) })
    // set prevStatistics (i.e. override values with same key or add):
    prevSmtStatistics = prevSmtStatistics ++ currentStatistics
    deltaStatistics
  }

  private def getDelta(pair: (String, String)): (String, Option[String]) = {
    val curValInt = toInt(pair._2)
    val prevValInt = prevSmtStatistics.get(pair._1) match {
      case Some(value) => toInt(value)
      case _ => Some(0) // value not found
    }
    val curValDouble = toDouble(pair._2)
    val prevValDouble = prevSmtStatistics.get(pair._1) match {
      case Some(value) => toDouble(value)
      case _ => Some(0.0) // value not found
    }
    (curValInt, prevValInt, curValDouble, prevValDouble) match {
      case (Some(curInt), Some(prevInt), _, _) => (pair._1, Some((curInt - prevInt).toString))
      case (_, _, Some(curDouble), Some(prevDouble)) => (pair._1, Some((curDouble - prevDouble).toString))
      case _ => (pair._1, None)
    }
  }

  private def toInt(str: String): Option[Int] = {
    try {
      Some(str.toInt)
    } catch {
      case e: NumberFormatException => None
    }
  }

  private def toDouble(str: String): Option[Double] = {
    try {
      Some(str.toDouble)
    } catch {
      case e: NumberFormatException => None
    }
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

  var main = v match {
    case m: ast.Method => new MethodRecord(m, s, pcs)
    case p: ast.Predicate => new PredicateRecord(p, s, pcs)
    case f: ast.Function => new FunctionRecord(f, s, pcs)
    case _ => null
  }
  insert(main)

  private def appendLog(r: SymbolicRecord): Unit = {
    if (branchingStack.isEmpty) {
      log = log :+ r
    } else {
      branchingStack.head.appendLog(r)
    }
  }

  @elidable(INFO)
  def insert(s: DataRecord): Int = {
    s.id = SymbExLogger.freshUid()
    appendLog(s)
    val openRecord = new OpenScopeRecord(s)
    insert(openRecord)
    s.id
  }

  @elidable(INFO)
  def insert(s: ScopingRecord): Int = {
    s.id = SymbExLogger.freshUid()
    s.timeMs = System.currentTimeMillis()
    appendLog(s)
    s.id
  }

  @elidable(INFO)
  def insertBranchPoint(possibleBranchesCount: Int): Int = {
    val branchingRecord = new BranchingRecord(possibleBranchesCount)
    branchingRecord.id = SymbExLogger.freshUid()
    appendLog(branchingRecord)
    branchingStack = branchingRecord :: branchingStack
    branchingRecord.id
  }

  @elidable(INFO)
  def switchToNextBranch(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingRecord.switchToNextBranch()
  }

  @elidable(INFO)
  def markReachable(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    branchingRecord.markReachable()
  }

  // TODO legacy
  @elidable(INFO)
  def collapse(v: ast.Node, n: Int): Unit = {
    val closeRecord = new CloseScopeRecord(n)
    insert(closeRecord)
  }

  @elidable(INFO)
  // TODO legacy
  def collapseBranchPoint(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
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
  override def insertBranchPoint(possibleBranchesCount: Int): Int = 0
  override def switchToNextBranch(uidBranchPoint: Int): Unit = {}
  override def collapse(v: ast.Node, n: Int): Unit = {}
  override def collapseBranchPoint(uidBranchPoint: Int): Unit = {}
}

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
