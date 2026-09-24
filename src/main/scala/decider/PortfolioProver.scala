// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Result}
import viper.silicon.state.terms.{Decl, Function, FunctionDecl, Sort, Term}
import viper.silicon.verifier.Verifier
import viper.silicon.{Config, Map, toMap}
import viper.silver.reporter.{InternalWarningMessage, Reporter}
import viper.silver.verifier.Model

import java.util.concurrent.{ExecutorService, Executors}
import scala.util.{Failure, Random, Success, Try}

object PortfolioProver {
  /** A portfolio is configured as a list of prover names separated by this string, e.g. "Z3-API,cvc5-API". */
  val separator = ","

  def memberNames(proverName: String): Seq[String] =
    proverName.split(separator).map(_.trim).filter(_.nonEmpty).toSeq

  def isPortfolio(proverName: String): Boolean = memberNames(proverName).size > 1

  /* Threads that run queries convert terms, which recurses on deep terms; they therefore get a stack as large as
   * Silicon's main thread (see build.sbt). */
  private val threadStackSize: Long = 128L * 1024 * 1024

  /* Like Try, but also captures fatal errors (e.g. stack overflows), so that the thread waiting for the outcome of
   * a task that runs on another thread is guaranteed to be woken up. */
  private def attempt[A](body: => A): Try[A] =
    try { Success(body) } catch { case t: Throwable => Failure(t) }
}

/** A prover that runs a portfolio of provers side by side.
  *
  * Everything that changes the prover state (declarations, assumptions, push/pop, options) is forwarded to every
  * member, so that all members always know the same facts. Queries (assert, check) are started on all members at
  * once: the answer of the first member to finish is returned, and the queries still running on the other members
  * are interrupted (see [[Prover.interrupt]]). Members that cannot be interrupted, such as the StdIO provers, delay
  * the answer until they finish or time out.
  */
class PortfolioProver(val members: Seq[Prover], reporter: Reporter)
    extends Prover
       with LazyLogging {

  require(members.nonEmpty, "A portfolio must consist of at least one prover")

  private val preambleReader = new SMTLib2PreambleReader
  private var executor: ExecutorService = _

  /* The members that answer queries, see setActiveMembers. All other members merely keep their state up to date. */
  private var activeMembers: Seq[Prover] = members

  /* The member whose answer to the most recent query was used; models and reasons for unknown results are its */
  private var lastAnswered: Prover = _

  /* Life cycle */

  def start(): Unit = {
    start(Verifier.config.proverArgs)
  }

  def start(userArgsString: Option[String]): Unit = {
    executor = Executors.newFixedThreadPool(members.size, (runnable: Runnable) => {
      val thread = new Thread(null, runnable, "portfolio-prover", PortfolioProver.threadStackSize)
      thread.setDaemon(true)
      thread
    })

    members foreach (_.start(userArgsString))
    emitMemberPreambles()
  }

  def reset(): Unit = {
    members foreach (_.reset())
    activeMembers = members
    lastAnswered = null
    emitMemberPreambles()
  }

  def stop(): Unit = {
    members foreach (_.stop())
    activeMembers = members
    lastAnswered = null

    if (executor != null) {
      executor.shutdownNow()
      executor = null
    }
  }

  /* The static preamble of a prover consists of options specific to that prover, so a portfolio has none of its
   * own (see also DefaultMainVerifier.emitStaticPreamble). Instead, every member receives its own preamble as soon
   * as it has been (re)started. */
  private def emitMemberPreambles(): Unit = members foreach { member =>
    member.comment(s"\n; ${member.staticPreamble}")
    preambleReader.emitPreamble(member.staticPreamble, member, true)

    if (Verifier.config.proverRandomizeSeeds()) {
      val options = member.randomizeSeedsOptions.map(key => s"(set-option :$key ${Random.nextInt(10000)})")
      preambleReader.emitPreamble(options, member, true)
    }
  }

  lazy val staticPreamble: String = "" /* See emitMemberPreambles */

  /** Restricts the members that answer queries to those whose names are given (None lifts the restriction). The
    * other members keep their state up to date nevertheless, so that they can be activated again at any time.
    * Must not be called while a query is running.
    */
  def setActiveMembers(names: Option[Seq[String]]): Unit = {
    activeMembers = names match {
      case Some(selected) => members.filter(member => selected.contains(member.name))
      case None => members
    }

    require(activeMembers.nonEmpty, s"None of the provers ${names.get.mkString(", ")} is a member of portfolio $name")
  }

  /** The names of the members that answer queries, or None if all of them do. */
  def activeMemberNames: Option[Seq[String]] =
    if (activeMembers.size == members.size) None else Some(activeMembers.map(_.name))

  lazy val randomizeSeedsOptions: Seq[String] = Seq() /* See emitMemberPreambles */

  /* Operations that are forwarded to all members */

  def emit(content: String): Unit = members foreach (_.emit(content))

  override def emit(contents: Iterable[String]): Unit = members foreach (_.emit(contents))

  def emitSettings(contents: Iterable[String]): Unit = members foreach (_.emitSettings(contents))

  def setOption(name: String, value: String): String = (members map (_.setOption(name, value))).head

  def assume(term: Term): Unit = members foreach (_.assume(term))

  def declare(decl: Decl): Unit = members foreach (_.declare(decl))

  def comment(content: String): Unit = members foreach (_.comment(content))

  def push(n: Int = 1, timeout: Option[Int] = None): Unit = members foreach (_.push(n, timeout))

  def pop(n: Int = 1): Unit = members foreach (_.pop(n))

  def pushPopScopeDepth: Int = members.head.pushPopScopeDepth

  def fresh(id: String, argSorts: Seq[Sort], resultSort: Sort): Function = {
    /* The first member creates the fresh symbol; the others merely declare it, so that all use the same name */
    val fun = members.head.fresh(id, argSorts, resultSort)
    members.tail foreach (_.declare(FunctionDecl(fun)))

    fun
  }

  def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {
    data match {
      case Some(Config.ProverStateSaturationTimeout(timeout, comment)) => saturate(timeout, comment)
      case None => /* Don't do anything */
    }
  }

  def saturate(timeout: Int, comment: String): Unit =
    onActive(_.saturate(timeout, comment)).awaitAll() foreach { case (_, outcome) => outcome.get }

  def interrupt(): Unit = members foreach (_.interrupt())

  def clearLastAssert(): Unit = {
    members foreach (_.clearLastAssert())
    lastAnswered = null
  }

  /* Queries */

  def assert(goal: Term, timeout: Option[Int] = None): Boolean = race(_.assert(goal, timeout))

  def check(timeout: Option[Int] = None): Result = race(_.check(timeout))

  /* Collects the outcomes of a task that runs on several members and lets the caller wait for the first and for all
   * of them. Waiting uses plain monitors rather than java.util.concurrent, since blocking on the latter inside a
   * ForkJoinPool worker thread (on which Silicon's verifiers run) makes the pool spawn compensation threads. */
  private class Outcomes[A](expected: Int) {
    private var outcomes = Vector.empty[(Prover, Try[A])]

    def add(member: Prover, outcome: Try[A]): Unit = synchronized {
      outcomes :+= ((member, outcome))
      notifyAll()
    }

    def awaitFirst(): (Prover, Try[A]) = synchronized {
      while (outcomes.isEmpty) wait()
      outcomes.head
    }

    def awaitAll(): Seq[(Prover, Try[A])] = synchronized {
      while (outcomes.size < expected) wait()
      outcomes
    }
  }

  private def onActive[A](task: Prover => A): Outcomes[A] = {
    val outcomes = new Outcomes[A](activeMembers.size)

    activeMembers foreach { member =>
      executor.execute(() => outcomes.add(member, PortfolioProver.attempt(task(member))))
    }

    outcomes
  }

  /* Runs the query on all active members at once, returns the answer of the first member to finish and interrupts
   * the others. Returns only once all of them are idle again, since their state must not change while they are busy. */
  private def race[A](query: Prover => A): A = {
    val outcomes = onActive(query)

    val (first, answer) = outcomes.awaitFirst()
    lastAnswered = first
    activeMembers filterNot (_ eq first) foreach (_.interrupt())

    outcomes.awaitAll() foreach { case (member, outcome) =>
      if (!(member eq first)) outcome.failed foreach { e =>
        val msg = s"Prover ${member.name} failed after being interrupted: ${e.getMessage}"
        reporter report InternalWarningMessage(msg)
        logger warn msg
      }
    }

    answer.get
  }

  /* Results of the most recent query */

  def hasModel(): Boolean = lastAnswered != null && lastAnswered.hasModel()

  def isModelValid(): Boolean = lastAnswered != null && lastAnswered.isModelValid()

  def getModel(): Model = lastAnswered.getModel()

  def getReasonUnknown(): String = if (lastAnswered == null) null else lastAnswered.getReasonUnknown()

  def statistics(): Map[String, String] = toMap(
    members.zipWithIndex flatMap { case (member, index) =>
      member.statistics() map { case (key, value) => (s"${member.name}_$index.$key", value) }
    })

  /* Miscellaneous */

  lazy val name: String = s"Portfolio(${members.map(_.name).mkString(PortfolioProver.separator)})"

  /* Versions are checked per member, see DefaultDeciderProvider.createProver */

  lazy val minVersion: Version = members.head.minVersion

  lazy val maxVersion: Option[Version] = members.head.maxVersion

  def version(): Version = members.head.version()

  def getAllDecls(): Seq[Decl] = members.head.getAllDecls()

  def getAllEmits(): Seq[String] = members.head.getAllEmits()
}
