// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger

import org.slf4j.LoggerFactory
import spray.json._
import viper.silicon.decider.PathConditionStack
import viper.silicon.logger.LogConfigProtocol._
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data._
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.logger.renderer.SimpleTreeRenderer
import viper.silicon.state.terms._
import viper.silicon.{Config, Map}
import viper.silver.ast
import viper.silver.ast.{Exp, Member}

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.immutable
import scala.util.{Failure, Success, Try}

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

/**
 * ================================
 * SymbExLogger Architecture
 * ================================
 * Overall concept:
 * 1) [[SymbExLogger]]:
 *    SymbExLogger is the root log for a verification run. Implementers of SymbExLogger define how to make a
 *    [[MemberSymbExLogger]]: the log for a method/function/predicate (member). Contains a map of members logs.
 *    The default implementation is [[NoopSymbExLog]], which ignores all log records. When the symbolic execution logger
 *    is enabled, [[SymbExLog]] is used instead. It instantiates the member loggers as MemberSymbExLog, which records
 *    all log records in memory.
 *    [[viper.silicon.verifier.MainVerifier]] owns the root SymbExLogger, from which member logs can be created.
 * 2) [[MemberSymbExLogger]]:
 *    Handles the log for a member. Most important methods: openScope/closeScope/insertBranchPoint. To 'start'
 *    a record use openScope, to finish the recording use closeScope. For each execution path, there should be a
 *    closeScope for each openScope. Due to branching this means that there might be multiple closeScopes for a
 *    openScope, because the scope has to be closed on each branch. However to support verification failures, the log
 *    does not have to be complete. In case of a missing close scope record, the scope will be closed immediately
 *    before an outer close scope record.
 *    The default implementation is [[NoopMemberSymbExLog]], which ignores all log records. When the symbolic execution
 *    logger is enabled, [[MemberSymbExLog]] is used instead, which records all log records in memory.
 *    Each [[viper.silicon.verifier.Verifier]] owns a [[MemberSymbExLog]] for the member it is currently verifying.
 *    [[viper.silicon.verifier.DefaultMainVerifier]] also owns a [[MemberSymbExLog]], since it also verifies members
 *    itself.
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
  * //val id = symbExLog.openScope(new CommentRecord(my_info, σ, c)
  * //symbExLog.closeScope(id)
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
  * // val uidJoin = symbExLog.openScope(joiningRecord)
  * After executing the block and joining the execution, the following call to the SymbExLogger is made to close the
  * join scope:
  * // symbExLog.closeScope(uidJoin)
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
  * // val uidBranchPoint = symbExLog.insertBranchPoint(2, Some(condition))
  * All records that will subsequently be inserted will be assigned to the first branch.
  * As soon as the execution of the first branch is complete, the logger needs to switch to the next branch:
  * // symbExLog.switchToNextBranch(uidBranchPoint)
  * When the execution of all branches is done, the branch point is concluded:
  * // symbExLog.endBranchPoint(uidBranchPoint)
  * Because the existence as well as non-existence of records on a branch does not imply reachability, the logger
  * needs to be explicitly informed for each branch that is reachable:
  * // symbExLog.markReachable(uidBranchPoint)
  */

case object SymbExLogger {
  def ofConfig(config: Config): SymbExLogger[_ <: MemberSymbExLogger] = {
    if(config.ideModeAdvanced())
      SymbExLog(parseLogConfig(config))
    else
      NoopSymbExLog
  }

  private lazy val textLogger = LoggerFactory.getLogger(classOf[SymbExLogger[_]])

  private def parseLogConfig(config: Config): LogConfig = {
    val logConfigPath = config.logConfig.getOrElse(return LogConfig.default())
    val source = Success(logConfigPath).map(path => scala.io.Source.fromFile(path))
    val fileContent = source.map(s => s.getLines().mkString)
    val jsonAst = fileContent.flatMap(content => Try(content.parseJson))
    val logConfig = jsonAst.flatMap(ast => Try(ast.convertTo[LogConfig]))
    logConfig match {
      case Success(convertedConfig) => convertedConfig
      case Failure(err) =>
        textLogger.warn(
          s"Could not parse the configuration for the symbolic execution logger at $logConfigPath: " +
          s"${err.getMessage} The default configuration will be used instead.")
        LogConfig.default()
    }
  }
}

abstract class SymbExLogger[Log <: MemberSymbExLogger]() {
  /** Collection of logged Method/Predicates/Functions. */
  protected var members: immutable.Map[ast.Member, Log] = Map.empty
  protected var closed: Boolean = false
  def isClosed: Boolean = closed
  protected val uidCounter: AtomicInteger = new AtomicInteger(0)

  protected def newEntityLogger(member: ast.Member, pcs: PathConditionStack): Log

  def freshUid(): Int = uidCounter.getAndIncrement()

  def whenEnabled(f: => Unit): Unit = f

  def logs: Iterable[Log] = members.values

  /** Add a new log for a method, function or predicate (member).
    *
    * @param member Either a MethodRecord, PredicateRecord or a FunctionRecord.
    * @param pcs    Current path conditions.
    */
  @elidable(INFO)
  def openMemberScope(member: ast.Member, pcs: PathConditionStack): Log = {
    val log = newEntityLogger(member, pcs)

    synchronized {
      if(isClosed) {
        // If we time out and close the log, but somehow manage to race to move on to a new member in time, the log is
        // closed so the records are not vacuously recorded, and the log is not added to the map of logs.
        log.close()
      } else {
        members += member -> log
      }
    }

    log.openMemberScope()
    log
  }

  def close(): Unit =
    synchronized {
      members.values.foreach(_.close())
    }
}

case object NoopSymbExLog extends SymbExLogger[NoopMemberSymbExLog.type] {
  override def newEntityLogger(member: Member, pcs: PathConditionStack): NoopMemberSymbExLog.type =
    NoopMemberSymbExLog

  override def whenEnabled(f: => Unit): Unit = {}

  override def openMemberScope(member: Member, pcs: PathConditionStack): NoopMemberSymbExLog.type =
    NoopMemberSymbExLog
}

case class SymbExLog(logConfig: LogConfig) extends SymbExLogger[MemberSymbExLog]() {
  override def newEntityLogger(member: ast.Member, pcs: PathConditionStack): MemberSymbExLog =
    new MemberSymbExLog(this, logConfig, member, pcs)

  /**
    * Simple string representation of the logs.
    */
  def toSimpleTreeString: String = {
    val simpleTreeRenderer = new SimpleTreeRenderer()
    simpleTreeRenderer.render(members.values)
  }
}

abstract class MemberSymbExLogger(log: SymbExLogger[_],
                                  val member: ast.Member,
                                  val pcs: PathConditionStack) {
  protected def appendDataRecord(r: DataRecord): Unit
  protected def appendScopingRecord(r: ScopingRecord, ignoreBranchingStack: Boolean = false): Unit
  protected def appendBranchingRecord(r: BranchingRecord): Unit

  protected def doSwitchToNextBranch(uidBranchPoint: Int): Unit
  protected def markBranchReachable(uidBranchPoint: Int): Unit
  protected def doEndBranchPoint(uidBranchPoint: Int): Unit

  def whenEnabled(f: => Unit): Unit = log.whenEnabled(f)

  /**
    * indicates whether this member's close was already closed
    */
  private var closed: Boolean = false
  def isClosed: Boolean = closed

  /**
    * Most recent output of (get-info :all-statistics) from the underlying prover
    */
  private var lastStatistics: Map[String, String] = Map.empty

  // Maps macros to their body
  private var _macros = Map[App, Term]()

  def close(): Unit =
    synchronized {
      closed = true
    }

  def whenOpen(f: => Unit): Unit =
    synchronized {
      if(!isClosed) f else ()
    }

  var main: MemberRecord = _

  def openMemberScope(): Unit = {
    main = member match {
      case m: ast.Method => new MethodRecord(m, pcs)
      case p: ast.Predicate => new PredicateRecord(p, pcs)
      case f: ast.Function => new FunctionRecord(f, pcs)
      case _ => ???
    }

    openScope(main)
  }

  /**
    * Inserts the record as well as a corresponding open scope record into the log
    *
    * @param s non-null record
    * @return id with which closeScope should be called
    */
  @elidable(INFO)
  def openScope(s: DataRecord): Int = {
    s.id = log.freshUid()
    whenOpen { appendDataRecord(s) }
    insert(new OpenScopeRecord(s))
    s.id
  }

  /**
    * Appends a scoping record to the log unless it's referenced data record is ignored
    *
    * @param s                    non-null scoping record
    * @param ignoreBranchingStack true if the record should always be inserted in the root level
    * @return id of the scoping record
    */
  @elidable(INFO)
  private def insert(s: ScopingRecord, ignoreBranchingStack: Boolean = false): Int = {
    s.id = log.freshUid()
    s.timeMs = System.currentTimeMillis()
    whenOpen { appendScopingRecord(s, ignoreBranchingStack) }
    s.id
  }

  /**
    * Creates and appends a branching record to the log. Branching records do not cause scopes.
    * Use `switchToNextBranch` to change from the current to the next branch and `endBranchPoint` to conclude the
    * branch point after all branches were visited.
    *
    * @param possibleBranchesCount number of branches that this branch point has but are not necessarily all reachable
    * @param condition             branch condition
    * @return id of the branching record
    */
  @elidable(INFO)
  def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term] = None, conditionExp: Option[Exp] = None): Int = {
    val branchingRecord = new BranchingRecord(possibleBranchesCount, condition, conditionExp)
    branchingRecord.id = log.freshUid()
    whenOpen { appendBranchingRecord(branchingRecord) }
    branchingRecord.id
  }

  @elidable(INFO)
  def switchToNextBranch(uidBranchPoint: Int): Unit = {
    whenEnabled { doSwitchToNextBranch(uidBranchPoint) }
  }

  /**
    * Marks the current branch of a specific branch point as being reachable
    *
    * @param uidBranchPoint id of the branching record
    */
  @elidable(INFO)
  def markReachable(uidBranchPoint: Int): Unit = {
    whenEnabled { markBranchReachable(uidBranchPoint) }
  }

  @elidable(INFO)
  def endBranchPoint(uidBranchPoint: Int): Unit = {
    whenEnabled { doEndBranchPoint(uidBranchPoint) }
  }

  /**
    * Ends the scope of a specific data record by inserting a corresponding close scope record into the log
    *
    * @param n id of the data record
    */
  @elidable(INFO)
  def closeScope(n: Int): Unit = {
    val closeRecord = new CloseScopeRecord(n)
    insert(closeRecord)
  }

  /**
    * Ends the scope of the member (i.e. main) by inserting a corresponding close scope record into the log
    */
  def closeMemberScope(): Unit = {
    val closeRecord = new CloseScopeRecord(main.id)
    // always insert this close scope record on the root log instead of at the correct place depending on branching stack:
    insert(closeRecord, ignoreBranchingStack = true)
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

  /**
    * Calculates the diff between the current and last statistics query.
    * The difference is calculated if value can be converted to an int or double
    *
    * @return map with the current statistics, and the differences (only containing values that could be converted)
    *         and keys with appended "-delta"
    */
  def deltaStatistics(currentStatistics: Map[String, String]): Map[String, String] = {
    val deltaStatistics = currentStatistics map getDelta filter { case (_, value) => value.nonEmpty } map {
      case (key, Some(value)) => (key + "-delta", value)
      case other => sys.error(s"Unexpected result pair $other")
    }
    whenEnabled { lastStatistics = lastStatistics ++ currentStatistics }
    currentStatistics ++ deltaStatistics
  }

  private def getDelta(pair: (String, String)): (String, Option[String]) = {
    val delta =
      Try { (pair._2.toInt - lastStatistics(pair._1).toInt).toString } orElse
      Try { (pair._2.toDouble - lastStatistics(pair._1).toDouble).toString }

    pair._1 -> delta.toOption
  }

  def macros(): Map[App, Term] = _macros

  @elidable(INFO)
  def addMacro(m: App, body: Term): Unit = whenEnabled {
    _macros = _macros + (m -> body)
  }
}

case object NoopMemberSymbExLog extends MemberSymbExLogger(null, null, null) {
  override def appendDataRecord(r: DataRecord): Unit = {}
  override def appendScopingRecord(r: ScopingRecord, ignoreBranchingStack: Boolean): Unit = {}
  override def appendBranchingRecord(r: BranchingRecord): Unit = {}
  override def markBranchReachable(uidBranchPoint: Int): Unit = {}
  override def doSwitchToNextBranch(uidBranchPoint: Int): Unit = {}
  override def doEndBranchPoint(uidBranchPoint: Int): Unit = {}

  override def whenEnabled(f: => Unit): Unit = {}

  override def openMemberScope(): Unit = {}
  override def openScope(s: DataRecord): Int = 0
  override def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term] = None, conditionExp: Option[Exp] = None): Int = 0
  override def markReachable(uidBranchPoint: Int): Unit = {}
  override def closeScope(n: Int): Unit = {}
  override def closeMemberScope(): Unit = {}
  override def setSMTQuery(query: Term): Unit = {}
  override def discardSMTQuery(): Unit = {}
}

class MemberSymbExLog(rootLog: SymbExLogger[MemberSymbExLog],
                      logConfig: LogConfig,
                      member: ast.Member,
                      pcs: PathConditionStack) extends MemberSymbExLogger(rootLog, member, pcs) {
  /** top level log entries for this member; these log entries were recorded consecutively without branching;
    * in case branching occured, one of these records is a BranchingRecord with all branches as field attached to it */
  var log: Vector[SymbolicRecord] = Vector[SymbolicRecord]()

  /** this stack keeps track of BranchingRecords while adding records to the log; as soon as all branches of a
    * BranchingRecord are done, logging has to switch back to the previous BranchingRecord */
  var branchingStack: List[BranchingRecord] = List[BranchingRecord]()

  /** if a record was ignored due to the logConfig, its ID is tracked here and corresponding open and close scope
    * records will be ignored too */
  var ignoredDataRecords: Set[Int] = Set()

  override def toString: String =
    new SimpleTreeRenderer().renderMember(this)

  def appendRecord(r: SymbolicRecord, ignoreBranchingStack: Boolean = false): Unit = {
    if (branchingStack.isEmpty || ignoreBranchingStack) {
      log = log :+ r
    } else {
      branchingStack.head.appendLog(r)
    }
  }

  override def appendDataRecord(r: DataRecord): Unit = {
    val shouldIgnore = logConfig.getRecordConfig(r) match {
      case Some(_) => logConfig.isBlackList
      case None => !logConfig.isBlackList
    }

    if (shouldIgnore) {
      ignoredDataRecords = ignoredDataRecords + r.id
    } else {
      appendRecord(r)
    }
  }

  override def appendScopingRecord(r: ScopingRecord, ignoreBranchingStack: Boolean): Unit = {
    if (!ignoredDataRecords.contains(r.refId)) {
      if (ignoreBranchingStack) {
        log = log :+ r
      } else {
        appendRecord(r)
      }
    }
  }

  override def appendBranchingRecord(r: BranchingRecord): Unit = {
    appendRecord(r)
    branchingStack +:= r
  }

  override def doSwitchToNextBranch(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingRecord.switchToNextBranch()
  }

  override def markBranchReachable(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    branchingRecord.markReachable()
  }

  override def doEndBranchPoint(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingStack = branchingStack.tail
  }
}