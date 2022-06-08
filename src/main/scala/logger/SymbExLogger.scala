// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger

import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import spray.json._
import viper.silicon.decider.PathConditionStack
import viper.silicon.logger.LogConfigProtocol._
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data._
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.logger.renderer.SimpleTreeRenderer
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.{Config, Map}
import viper.silver.ast
import viper.silver.ast.Exp

import java.nio.file.{Files, Path, Paths}
import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.mutable.ArrayBuffer
import scala.util.{Failure, Success, Try}

/* TODO: InsertionOrderedSet is used by the logger, but the insertion order is
 *       probably irrelevant for logging. I.e. it might be ok if these sets were
 *       traversed in non-deterministic order.
 */

/**
  * ================================
  * SymbExLogger Usage
  * ================================
  * The SymbExLogger has to be enabled by passing `--ideModeAdvanced` to Silicon.
  * Unless otherwise specified, the default logConfig will be used (viper.silicon.logger.LogConfig.default()):
  * All logged records will be included in the report, but store, heap, and path conditions will be omitted.
  *
  * A custom logConfig can be used by passing `--logConfig <pathToLogConfig>` to Silicon. The logConfig has to be valid
  * JSON in the following format:
  * {
  *   "isBlackList": false,
  *   "includeStore": false,
  *   "includeHeap": false,
  *   "includeOldHeap": false,
  *   "includePcs": false,
  *   "recordConfigs": [
  *     {
  *       "kind": "method"
  *     },
  *     {
  *       "kind": "execute",
  *       "value": "a := 1"
  *     }
  *   ]
  * }
  *
  * isBlackList: specifies whether recordConfigs should be interpreted as a black- or whitelist
  * includeStore: specifies whether store information for each record (that offers it) should be included
  * includeHeap: specifies whether heap information for each record (that offers it) should be included
  * includeOldHeap: specifies whether old heap information for each record (that offers it) should be included
  * includePcs: specifies whether path condition information for each record (that offers it) should be included
  * recordConfigs: array of recordConfig
  * recordConfig.kind: string with which each SymbolicRecord.toTypeString() is matched against
  * recordConfig.value: optional string with which each SymbolicRecord.toSimpleString() is matched against
  *
  * Therefore, the above example leads to the following logger behavior:
  * - No store, heap, old heap, and path condition information will be present in the report
  * - By interpreting recordConfigs as whitelist, all records of type MethodRecord will be included in the report as
  *   well as any ExecuteRecord with statement "a := 1" (all other ExecuteRecords will be omitted)
  */

/*
 * ================================
 * SymbExLogger Architecture
 * ================================
 * Overall concept:
 * 1) SymbExLogger Object:
 *    Is used as interface to access the logs. Code from this file that is used in Silicon
 *    should only be used via SymbExLogger. Contains a list of SymbLog, one SymbLog
 *    per method/function/predicate (member). The method 'currentLog()' gives access to the log
 *    of the currently executed member.
 * 2) SymbLog:
 *    Contains the log for a member. Most important methods: openScope/closeScope/insertBranchPoint. To 'start'
 *    a record use openScope, to finish the recording use closeScope. For each execution path, there should be a
 *    closeScope for each openScope. Due to branching this means that there might be multiple closeScopes for a
 *    openScope, because the scope has to be closed on each branch. However to support verification failures, the log
 *    does not have to be complete. In case of a missing close scope record, the scope will be closed immediately
 *    before an outer close scope record.
 * 3) Records:
 *    There are scoping records representing open and close scope in the log. These records will be automatically
 *    inserted in the log by SymbExLogger depending on other records.
 *    Structural records represent branching and joining in the resulting log. JoiningRecords are inserted as regular
 *    data records, BranchingRecords are inserted using the special interface (insertBranchPoint, markReachable,
 *    switchToNextBranch, and endBranchPoint).
 *    Data records represent symbolic primitives (execute, evalute, consume, produce) as well as executions of some
 *    algorithms of the symbolic execution engine. Inserting a data record automatically creates a scope for it. Each
 *    subsequent log entry is assumped to be in the scope until scopeClose is invoked.
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
 *      WellformednessCheck null
 *      execute var a: Int
 *      execute a := 1
 *        evaluate 1
 *      execute a := a + 2
 *        evaluate a + 2
 *          evaluate a
 *          evaluate 2
 *
 *    The order of insert/collapse is as follows:
 *    openScope(method m),
 *    openScope(WellformednessCheck null), closeScope(WellformednessCheck null),
 *    openScope(execute var a), closeScope(execute var a), openScope(execute a := 1), openScope(evaluate 1),
 *    closeScope(evaluate 1), closeScope(execute a := 1),
 *    openScope(execute a := a + 2), openScope(evaluate a + 2), openScope(evaluate a) closeScope(evaluate a),
 *    openScope(evaluate 2), closeScope(evaluate 2), closeScope(evaluate a + 2), closeScope(execute a := a + 2),
 *    closeScope(method m)
 *
 *    CloseScope basically 'removes one indentation', i.e., brings you one level higher in the tree.
 */

/**
  * ================================
  * GUIDE FOR ADDING RECORDS TO SymbExLogger
  * ================================
  *
  * SymbExLogger records calls to several symbolic primitives (execute, evalute, produce, consume) as well as algorithms
  * of Silicon. By default, only the current state, context and parameters of the primitives are stored (if configured
  * in logConfig).
  * If you want to get more information from certain structures, there are several ways to store additional
  * info:
  *
  * 1) Store the information as a CommentRecord.
  * 2) Implement a customized record.
  *
  * Use of CommentRecord (1):
  * At the point in the code where you want to add the comment, call
  * //val id = SymbExLogger.currentLog().openScope(new CommentRecord(my_info, σ, c)
  * //SymbExLogger.currentLog().closeScope(id)
  * σ is the current state (AnyRef, but should be of type State[_,_,_] usually), my_info
  * is a string that contains the information you want to store, c is the current
  * context. If you want to store more information than just a string, consider (2).
  *
  * Use of custom Records (2):
  * For already existing examples of data records, have look at records/data. In particular ProverAssertRecord might be
  * of interested, because it shows how additional info can be stored and inserted into RecordData during report
  * creation.
  * Inserting new structure records might be a bit more involved, depending on the use case.
  * As an example, the joining (e.g. occurring in pure conditional expressions) is discussed next:
  * Silicon uses Joiner to join execution after an execution block. A JoiningRecord is created at the beginning of the
  * Joiner and added to the log by calling:
  * // val uidJoin = SymbExLogger.currentLog().openScope(joiningRecord)
  * After executing the block and joining the execution, the following call to the SymbExLogger is made to close the
  * join scope:
  * // SymbExLogger.currentLog().closeScope(uidJoin)
  * Although JoiningRecord is a structural record and joining in symbolic execution has significant impact on the
  * execution structure, JoiningRecord behalves almost as a data record in SymbExLogger:
  * Due to the design that each data record (and joining record) causes a scope and the scope contains all
  * subexpressions, it naturally follows that branching records and their branches inside a join scope will be joined
  * because they are part of join's scope and the scope eventually ends.
  * Hence, of more interest is branching (which most likely occurs in every join scope):
  * If the execution is branched (occurs in Brancher as well as in Executor when following more than one branch) the
  * logger has to be informed about it in order that records on the individual branches are correctly logged.
  * To do so, the following call creates a new branch point with a number of branches that result out of it (but aren't
  * necessarily all reachable):
  * // val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(2, Some(condition))
  * All records that will subsequently be inserted will be assigned to the first branch.
  * As soon as the execution of the first branch is complete, the logger needs to switch to the next branch:
  * // SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
  * When the execution of all branches is done, the branch point is concluded:
  * // SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
  * Because the existence as well as non-existence of records on a branch does not imply reachability, the logger
  * needs to be explicitly informed for each branch that is reachable:
  * // SymbExLogger.currentLog().markReachable(uidBranchPoint)
  */

object SymbExLogger {
  /** Collection of logged Method/Predicates/Functions. **/
  val memberList: ArrayBuffer[SymbLog] = ArrayBuffer()
  var _currentLog: ThreadLocal[Option[SymbLog]] = ThreadLocal.withInitial(() => None)

  private val uidCounter = new AtomicInteger(0)

  var enabled = false
  var logConfig: LogConfig = LogConfig.default()
  var listenerProvider: LogConfig => SymbLogListener = new InMemorySymbLog(_)

  def freshUid(): Int = uidCounter.getAndIncrement()

  /** Add a new log for a method, function or predicate (member).
    *
    * @param member Either a MethodRecord, PredicateRecord or a FunctionRecord.
    * @param s      Current state. Since the body of the method (predicate/function) is not yet
    *               executed/logged, this is usually the empty state (use Σ(Ø, Ø, Ø) for empty
    *               state).
    * @param pcs    Current path conditions.
    */
  @elidable(INFO)
  def openMemberScope(member: ast.Member, s: State, pcs: PathConditionStack): Unit = {
    val log = new SymbLog(listenerProvider(logConfig), member, s, pcs)
    memberList.synchronized { memberList += log }
    _currentLog.set(Some(log))
  }

  /** Use this method to access the current log, e.g., to access the log of the method
    * that gets currently symbolically executed.
    *
    * @return Returns the current method, predicate or function that is being logged.
    */
  def currentLog(): SymbLog = {
    if (enabled)
      _currentLog.get.get
    else NoopSymbLog
  }

  @elidable(INFO)
  def closeMemberScope(): Unit = {
    if (enabled) {
      currentLog().closeMemberScope()
      _currentLog.set(None)
    }
  }

  /**
    * Passes config from Silicon to SymbExLogger.
    *
    * @param c Config of Silicon.
    */
  def setConfig(c: Config): Unit = {
    setEnabled(c.ideModeAdvanced())
    logConfig = parseLogConfig(c)
  }

  def setListenerProvider(listener: LogConfig => SymbLogListener): Unit =
    listenerProvider = listener

  @elidable(INFO)
  private def setEnabled(b: Boolean): Unit = {
    enabled = b
  }

  private def parseLogConfig(c: Config): LogConfig = {
    var logConfigPath = Try(c.logConfig())
    logConfigPath = logConfigPath.filter(path => Files.exists(Paths.get(path)))
    val source = logConfigPath.map(path => scala.io.Source.fromFile(path))
    val fileContent = source.map(s => s.getLines().mkString)
    val jsonAst = fileContent.flatMap(content => Try(content.parseJson))
    val logConfig = jsonAst.flatMap(ast => Try(ast.convertTo[LogConfig]))
    logConfig match {
      case Success(convertedConfig) => convertedConfig
      case Failure(_) => LogConfig.default()
    }
  }

  /**
    * Simple string representation of the logs.
    */
  def toSimpleTreeString: String = {
    if (enabled) {
      val simpleTreeRenderer = new SimpleTreeRenderer()
      simpleTreeRenderer.render(memberList.map(_.listener).collect { case l: InMemorySymbLog => l })
    } else ""
  }

  /** Path to the file that is being executed. Is used for UnitTesting. **/
  var filePath: Path = _

  /**
    * Resets the SymbExLogger-object, to make it ready for a new file.
    * Only needed when several files are verified together (e.g., sbt test).
    */
  def reset(): Unit = {
    memberList.clear()
    uidCounter.set(0)
    filePath = null
    logConfig = LogConfig.default()
    listenerProvider = new InMemorySymbLog(_)
  }

  def resetMemberList(): Unit = {
    memberList.clear()
  }
}

//========================= SymbLog ========================

trait SymbLogListener {
  def appendDataRecord(symbLog: SymbLog, r: DataRecord): Unit
  def appendScopingRecord(symbLog: SymbLog, r: ScopingRecord, ignoreBranchingStack: Boolean = false): Unit
  def appendBranchingRecord(symbLog: SymbLog, r: BranchingRecord): Unit

  def switchToNextBranch(symbLog: SymbLog, uidBranchPoint: Int): Unit
  def markBranchReachable(symbLog: SymbLog, uidBranchPoint: Int): Unit
  def endBranchPoint(symbLog: SymbLog, uidBranchPoint: Int): Unit
}

class InMemorySymbLog(config: LogConfig) extends SymbLogListener {
  /** top level log entries for this member; these log entries were recorded consecutively without branching;
   * in case branching occured, one of these records is a BranchingRecord with all branches as field attached to it */
  var log: Vector[SymbolicRecord] = Vector[SymbolicRecord]()

  /** this stack keeps track of BranchingRecords while adding records to the log; as soon as all branches of a
   * BranchingRecord are done, logging has to switch back to the previous BranchingRecord */
  var branchingStack: List[BranchingRecord] = List[BranchingRecord]()

  /** if a record was ignored due to the logConfig, its ID is tracked here and corresponding open and close scope
   * records will be ignored too */
  var ignoredDataRecords: Set[Int] = Set()

  def appendRecord(r: SymbolicRecord, ignoreBranchingStack: Boolean = false): Unit = {
    if (branchingStack.isEmpty || ignoreBranchingStack) {
      log = log :+ r
    } else {
      branchingStack.head.appendLog(r)
    }
  }

  override def appendDataRecord(symbLog: SymbLog, r: DataRecord): Unit = {
    val shouldIgnore = config.getRecordConfig(r) match {
      case Some(_) => config.isBlackList
      case None => !config.isBlackList
    }

    if(shouldIgnore) {
      ignoredDataRecords = ignoredDataRecords + r.id
    } else {
      appendRecord(r)
    }
  }

  override def appendScopingRecord(symbLog: SymbLog, r: ScopingRecord, ignoreBranchingStack: Boolean): Unit = {
    if(!ignoredDataRecords.contains(r.refId)) {
      if(ignoreBranchingStack) {
        log = log :+ r
      } else {
        appendRecord(r)
      }
    }
  }

  override def appendBranchingRecord(symbLog: SymbLog, r: BranchingRecord): Unit = {
    appendRecord(r)
    branchingStack +:= r
  }

  override def switchToNextBranch(symbLog: SymbLog, uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingRecord.switchToNextBranch()
  }

  override def markBranchReachable(symbLog: SymbLog, uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    branchingRecord.markReachable()
  }

  override def endBranchPoint(symbLog: SymbLog, uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingStack = branchingStack.tail
  }
}

/**
  * Concept: One object of SymbLog per Method/Predicate/Function. SymbLog
  * is used in the SymbExLogger-object.
  */
class SymbLog(val listener: SymbLogListener, val v: ast.Member, val s: State, val pcs: PathConditionStack) {
  val logger: Logger =
    Logger(LoggerFactory.getLogger(s"${this.getClass.getName}"))

  /**
    * indicates whether this member's close was already closed
    */
  private var isClosed: Boolean = false

  // Maps macros to their body
  private var _macros = Map[App, Term]()

  val main: MemberRecord = v match {
    case m: ast.Method => new MethodRecord(m, s, pcs)
    case p: ast.Predicate => new PredicateRecord(p, s, pcs)
    case f: ast.Function => new FunctionRecord(f, s, pcs)
    case _ => null
  }

  openScope(main)

  /**
    * Inserts the record as well as a corresponding open scope record into the log
    * @param s non-null record
    * @return id with which closeScope should be called
    */
  @elidable(INFO)
  def openScope(s: DataRecord): Int = {
    s.id = SymbExLogger.freshUid()
    listener.appendDataRecord(this, s)
    insert(new OpenScopeRecord(s))
    s.id
  }

  /**
    * Appends a scoping record to the log unless it's referenced data record is ignored
    * @param s non-null scoping record
    * @param ignoreBranchingStack true if the record should always be inserted in the root level
    * @return id of the scoping record
    */
  @elidable(INFO)
  private def insert(s: ScopingRecord, ignoreBranchingStack: Boolean = false): Int = {
    s.id = SymbExLogger.freshUid()
    s.timeMs = System.currentTimeMillis()
    listener.appendScopingRecord(this, s, ignoreBranchingStack)
    s.id
  }

  /**
    * Creates and appends a branching record to the log. Branching records do not cause scopes.
    * Use `switchToNextBranch` to change from the current to the next branch and `endBranchPoint` to conclude the
    * branch point after all branches were visited.
    * @param possibleBranchesCount number of branches that this branch point has but are not necessarily all reachable
    * @param condition branch condition
    * @return id of the branching record
    */
  @elidable(INFO)
  def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term] = None, conditionExp: Option[Exp] = None): Int = {
    val branchingRecord = new BranchingRecord(possibleBranchesCount, condition, conditionExp)
    branchingRecord.id = SymbExLogger.freshUid()
    listener.appendBranchingRecord(this, branchingRecord)
    branchingRecord.id
  }

  /**
    * Changes from the current to the next branch of a specific branch point
    * @param uidBranchPoint id of the branching record
    */
  @elidable(INFO)
  def switchToNextBranch(uidBranchPoint: Int): Unit = {
    listener.switchToNextBranch(this, uidBranchPoint)
  }

  /**
    * Marks the current branch of a specific branch point as being reachable
    * @param uidBranchPoint id of the branching record
    */
  @elidable(INFO)
  def markReachable(uidBranchPoint: Int): Unit = {
    listener.markBranchReachable(this, uidBranchPoint)
  }

  /**
    * Ends the scope of a specific data record by inserting a corresponding close scope record into the log
    * @param n id of the data record
    */
  @elidable(INFO)
  def closeScope(n: Int): Unit = {
    val closeRecord = new CloseScopeRecord(n)
    insert(closeRecord)
  }

  /**
    * Concludes a specific branch point (which normaly happens after visiting all branches belonging to the branch point)
    * @param uidBranchPoint id of the branch point
    */
  @elidable(INFO)
  def endBranchPoint(uidBranchPoint: Int): Unit = {
    listener.endBranchPoint(this, uidBranchPoint)
  }

  /**
    * Ends the scope of the member (i.e. main) by inserting a corresponding close scope record into the log
    */
  def closeMemberScope(): Unit = {
    if (isClosed) {
      return
    }
    val closeRecord = new CloseScopeRecord(main.id)
    // always insert this close scope record on the root log instead of at the correct place depending on branching stack:
    insert(closeRecord, ignoreBranchingStack = true)
    isClosed = true
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

  def macros(): Map[App, Term] = _macros

  @elidable(INFO)
  def addMacro(m: App, body: Term): Unit = {
    _macros = _macros + (m -> body)
  }

  override def toString: String = listener match {
    case log: InMemorySymbLog => new SimpleTreeRenderer().renderMember(log)
    case _ => super.toString
  }
}

object NoopSymbLog extends SymbLog(null, null, null, null) {
  override def openScope(s: DataRecord): Int = 0
  override def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term], conditionExp: Option[Exp]): Int = 0
  override def switchToNextBranch(uidBranchPoint: Int): Unit = {}
  override def markReachable(uidBranchPoint: Int): Unit = {}
  override def closeScope(n: Int): Unit = {}
  override def endBranchPoint(uidBranchPoint: Int): Unit = {}
  override def closeMemberScope(): Unit = {}
}
