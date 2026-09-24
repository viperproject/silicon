// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.LazyLogging
import io.github.cvc5.{CVC5ApiException, CVC5ParserException, InputParser, Solver, SymbolManager, TermManager, Result => Cvc5Result}
import io.github.cvc5.modes.InputLanguage
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Result, Sat, Unknown, Unsat}
import viper.silicon.reporting.ProverInteractionFailed
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms.{App, Decl, Fun, FunctionDecl, Sort, Term, sorts}
import viper.silicon.verifier.Verifier
import viper.silicon.{Config, Map, toMap}
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage, Reporter}
import viper.silver.verifier.{Model, DefaultDependency => SilDefaultDependency}

import java.io.PrintWriter
import scala.jdk.CollectionConverters.IteratorHasAsScala

object Cvc5ProverAPI {
  val name = "cvc5-API"
  /* Before 1.3.3, the Java API's registry of native objects was not thread-safe, which crashes cvc5 when several
   * verifiers use it in parallel. */
  val minVersion: Version = Version("1.3.3")
  val maxVersion: Option[Version] = None
  val dependencies: Seq[SilDefaultDependency] = Seq(SilDefaultDependency("cvc5", minVersion.version, "https://github.com/cvc5/cvc5"))
  val staticPreamble: String = Cvc5ProverStdIO.staticPreamble
  val randomizeSeedsOptions: Seq[String] = Cvc5ProverStdIO.randomizeSeedsOptions

  /* Options that limit the effort spent on a single query, see setTimeout and interrupt */
  val resourceLimitOption = "reproducible-resource-limit"
  val timeLimitOption = "tlimit-per"

  /* Options that control where cvc5 writes diagnostic output, see start */
  val verbosityOption = "verbosity"
  val errorChannelOption = "err"
  val nullDevice: String = if (System.getProperty("os.name").toLowerCase.contains("win")) "NUL" else "/dev/null"
}

/** Binding to cvc5 via its Java API, i.e. cvc5 runs inside Silicon's JVM.
  *
  * Terms and declarations are rendered to SMT-LIB text by the same converter the StdIO provers use, and that text
  * is executed by cvc5's own SMT-LIB parser. The interaction with cvc5 is thus the same as for [[Cvc5ProverStdIO]],
  * but there is no separate process and no piping, and queries can be interrupted (see [[interrupt]]).
  *
  * Note that the Java API does not free native objects (commands, results, terms, ...) automatically, but keeps
  * every object in a global registry until its deletePointer method is called. Objects are therefore freed
  * explicitly as soon as they are no longer needed.
  */
class Cvc5ProverAPI(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory,
                    reporter: Reporter)
    extends Prover
       with LazyLogging {

  /* protected */ var pushPopScopeDepth = 0
  protected var lastTimeout: Int = -1
  protected var logfileWriter: PrintWriter = _
  protected var termManager: TermManager = _
  protected var solver: Solver = _
  protected var symbolManager: SymbolManager = _
  protected var parser: InputParser = _
  protected var allDecls: Seq[Decl] = Seq()
  protected var allEmits: Seq[String] = Seq()

  var lastReasonUnknown: String = _
  var lastModel: String = _

  /* Interrupt support, see interrupt(). Both fields are guarded by queryLock. */
  private val queryLock = new Object
  private var queryRunning = false
  private var queryInterrupted = false

  def version(): Version = {
    /* Development versions are reported as e.g. "1.3.0-dev.12.abc", of which only the leading part is a version */
    Version(solver.getVersion.split('-').head)
  }

  def start(): Unit = {
    start(Verifier.config.proverArgs)
  }

  def start(userArgsString: Option[String]): Unit = {
    if (solver != null) {
      throw new AssertionError("stop() should be called between any pair of start() calls")
    }
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = if (!Verifier.config.outputProverLog) null else viper.silver.utility.Common.PrintWriter(Verifier.config.proverLogFile(uniqueId).toFile)
    termManager = new TermManager()
    solver = new Solver(termManager)
    symbolManager = new SymbolManager(termManager)
    parser = new InputParser(solver, symbolManager)

    /* Whenever cvc5 suppresses diagnostic output because the verbosity is too low, it nevertheless formats the
     * output, terms included, into a stream object shared by the whole process. Formatting a term reads and writes
     * per-stream settings, which is not thread-safe, so solvers used in parallel (by different verifiers) corrupt
     * the memory of that stream; this was observed with quantifiers that are alpha-equivalent to earlier ones.
     * Diagnostic output is therefore enabled, but sent to a file stream owned by this solver that discards it. */
    solver.setOption(Cvc5ProverAPI.verbosityOption, "2")
    solver.setOption(Cvc5ProverAPI.errorChannelOption, Cvc5ProverAPI.nullDevice)
    comment(s"(set-option :${Cvc5ProverAPI.verbosityOption} 2) (set-option :${Cvc5ProverAPI.errorChannelOption} ${Cvc5ProverAPI.nullDevice})")

    userArgsString foreach applyCommandLineArguments
  }

  /* cvc5 cannot be given command-line arguments when it is used via its API. Arguments of the forms
   * --name=value, --name and --no-name are therefore translated to the corresponding options. */
  protected def applyCommandLineArguments(args: String): Unit = {
    val msg = s"Additional command-line arguments are $args"
    reporter report ConfigurationConfirmation(msg)
    logger debug msg

    val nameValue = """--([^=\s]+)=(\S+)""".r
    val flag = """--(\S+)""".r

    args.trim.split(' ').map(_.trim).filter(_.nonEmpty) foreach {
      case nameValue(name, value) => setSolverOption(name, value)
      case flag(name) if name.startsWith("no-") => setSolverOption(name.substring(3), "false")
      case flag(name) => setSolverOption(name, "true")
      case other =>
        val msg = s"Ignoring command-line argument '$other', which cannot be translated to a cvc5 option"
        reporter report InternalWarningMessage(msg)
        logger warn msg
    }
  }

  def reset(): Unit = {
    stop()
    start()
  }

  def stop(): Unit = {
    if (logfileWriter != null) {
      logfileWriter.close()
      logfileWriter = null
    }

    /* Objects are released in reverse order of creation, since each depends on the ones created before it */
    if (parser != null) { parser.deletePointer(); parser = null }
    if (symbolManager != null) { symbolManager.deletePointer(); symbolManager = null }
    if (solver != null) { solver.deletePointer(); solver = null }
    if (termManager != null) { termManager.deletePointer(); termManager = null }

    lastModel = null
    lastReasonUnknown = null
    allDecls = Seq()
    allEmits = Seq()
    preambleAssumptions = Seq()
  }

  def push(n: Int = 1, timeout: Option[Int] = None): Unit = {
    setTimeout(timeout)
    pushPopScopeDepth += n
    logToFile((if (n == 1) "(push)" else s"(push $n)") + " ; " + pushPopScopeDepth)
    solver.push(n)
  }

  def pop(n: Int = 1): Unit = {
    logToFile((if (n == 1) "(pop)" else s"(pop $n)") + " ; " + pushPopScopeDepth)
    pushPopScopeDepth -= n
    solver.pop(n)
  }

  def emit(content: String): Unit = {
    if (debugMode) {
      allEmits :+= content
    }
    execute(content)
  }

  def getAllEmits(): Seq[String] = allEmits

  override def emitSettings(contents: Iterable[String]): Unit = emit(contents)

  override def setOption(name: String, value: String): String = {
    val oldVal =
      try { solver.getOption(name) }
      catch { case _: CVC5ApiException => throw ProverInteractionFailed(uniqueId, s"Prover does not support option $name") }

    emit(s"(set-option :$name $value)")

    oldVal
  }

  /* Executes SMT-LIB commands via cvc5's parser. As for the StdIO provers, every command must succeed. */
  protected def execute(commands: String): Unit = {
    logToFile(commands)

    try {
      parser.setStringInput(InputLanguage.SMT_LIB_2_6, commands, uniqueId)

      var command = parser.nextCommand()
      while (!command.isNull) {
        val output =
          try { command.invoke(solver, symbolManager).trim }
          finally { command.deletePointer() }

        if (output.nonEmpty && output != "success") {
          throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover. Expected 'success' but found: $output")
        }

        command = parser.nextCommand()
      }
      command.deletePointer()
    } catch {
      case e: CVC5ParserException =>
        throw ProverInteractionFailed(uniqueId, s"Prover could not parse '$commands': ${e.getMessage}")
    }
  }

  def assume(term: Term): Unit = {
    assume(termConverter.convert(term))
  }

  def assume(term: String): Unit = {
    execute("(assert " + term + ")")
  }

  def assert(goal: Term, timeout: Option[Int] = None): Boolean =
    assert(termConverter.convert(goal), timeout)

  def assert(goal: String, timeout: Option[Int]): Boolean = {
    val (result, duration) = Verifier.config.assertionMode() match {
      case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal, timeout)
      case Config.AssertionMode.PushPop => assertUsingPushPop(goal, timeout)
    }

    comment(s"${viper.silver.reporter.format.formatMillisReadably(duration)}")

    result
  }

  protected def assertUsingPushPop(goal: String, timeout: Option[Int]): (Boolean, Long) = {
    push()
    setTimeout(timeout)

    assume("(not " + goal + ")")

    val startTime = System.currentTimeMillis()
    val (res, explanation) = checkSat()
    val endTime = System.currentTimeMillis()
    val result = res == Unsat

    if (!result) {
      retrieveAndSaveModel()
      retrieveReasonUnknown(explanation)
    }

    pop()

    (result, endTime - startTime)
  }

  protected def assertUsingSoftConstraints(goal: String, timeout: Option[Int]): (Boolean, Long) = {
    setTimeout(timeout)

    val guard = fresh("grd", Nil, sorts.Bool)
    val guardApp = termConverter.convert(App(guard, Nil))

    assume(s"(=> $guardApp (not $goal))")

    val startTime = System.currentTimeMillis()
    logToFile(s"(check-sat $guardApp)")
    parser.setStringInput(InputLanguage.SMT_LIB_2_6, guardApp, uniqueId)
    val guardTerm = parser.nextTerm()
    val (res, _) =
      try { runQuery(solver.checkSatAssuming(guardTerm)) }
      finally { guardTerm.deletePointer() }
    val endTime = System.currentTimeMillis()
    val result = res == Unsat

    if (!result) {
      retrieveAndSaveModel()
    }

    (result, endTime - startTime)
  }

  def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {
    data match {
      case Some(Config.ProverStateSaturationTimeout(timeout, comment)) => saturate(timeout, comment)
      case None => /* Don't do anything */
    }
  }

  def saturate(timeout: Int, comment: String): Unit = {
    this.comment(s"State saturation: $comment")
    setTimeout(Some(timeout))
    checkSat()
  }

  def check(timeout: Option[Int] = None): Result = {
    setTimeout(timeout)

    checkSat()._1
  }

  private def checkSat(): (Result, Option[String]) = {
    logToFile("(check-sat)")
    runQuery(solver.checkSat())
  }

  /* Runs a query on the solver while recording that it is running, so that a concurrent call to interrupt()
   * only affects the solver while a query is actually in progress. If the query was interrupted, the regular
   * per-query limit is restored afterwards. Returns the result and, if it is unknown, cvc5's explanation. */
  private def runQuery(query: => Cvc5Result): (Result, Option[String]) = {
    queryLock.synchronized {
      queryRunning = true
      queryInterrupted = false
    }

    try {
      val res = query

      try {
        comment(res.toString)

        if (res.isSat) (Sat, None)
        else if (res.isUnsat) (Unsat, None)
        else (Unknown, Some(res.getUnknownExplanation.toString))
      } finally {
        res.deletePointer()
      }
    } finally {
      queryLock.synchronized {
        queryRunning = false

        if (queryInterrupted) {
          queryInterrupted = false
          applyTimeout()
        }
      }
    }
  }

  /** Interrupts the query currently running on this prover, if any, typically from another thread.
    *
    * cvc5's API offers no dedicated way of interrupting a query, but a running query does observe changes to its
    * resource limit (unlike changes to its time limit, which cvc5 only reads when a query starts), and that option
    * is one of the few that cvc5 allows to change once the solver is initialised. Setting the limit to a single
    * resource unit therefore makes the running query return (with an unknown result) right away, after which
    * runQuery restores the regular limit.
    */
  def interrupt(): Unit = {
    queryLock.synchronized {
      if (queryRunning && !queryInterrupted) {
        queryInterrupted = true
        setSolverOption(Cvc5ProverAPI.resourceLimitOption, "1")
      }
    }
  }

  protected def retrieveAndSaveModel(): Unit = {
    if (Verifier.config.counterexample.toOption.isDefined) {
      logToFile("(get-model)")
      val declaredSorts = symbolManager.getDeclaredSorts
      val declaredTerms = symbolManager.getDeclaredTerms
      lastModel =
        try { solver.getModel(declaredSorts, declaredTerms).trim }
        catch { case _: CVC5ApiException => null } /* No model is available, e.g. because the result was unknown */
        finally {
          declaredSorts foreach (_.deletePointer())
          declaredTerms foreach (_.deletePointer())
        }
    }
  }

  protected def retrieveReasonUnknown(explanation: Option[String]): Unit = {
    if (Verifier.config.reportReasonUnknown()) {
      lastReasonUnknown = explanation.orNull
    }
  }

  override def hasModel(): Boolean = {
    lastModel != null
  }

  override def isModelValid(): Boolean = {
    lastModel != null
  }

  override def getModel(): Model = Model(lastModel)

  override def getReasonUnknown(): String = lastReasonUnknown

  override def clearLastAssert(): Unit = {
    lastReasonUnknown = null
    lastModel = null
  }

  def statistics(): Map[String, String] = {
    /* As for the StdIO provers, only numeric statistics are of interest */
    val statistics = solver.getStatistics

    try {
      val entries = statistics.iterator().asScala flatMap { entry =>
        val stat = entry.getValue

        try {
          if (stat.isInt) Some(entry.getKey -> stat.getInt.toString)
          else if (stat.isDouble) Some(entry.getKey -> stat.getDouble.toString)
          else None
        } finally {
          stat.deletePointer()
        }
      }

      toMap(entries.toSeq.sortBy(_._1))
    } finally {
      statistics.deletePointer()
    }
  }

  def comment(str: String): Unit = {
    val sanitisedStr =
      str.replaceAll("\r", "")
         .replaceAll("\n", "\n; ")

    logToFile("; " + sanitisedStr)
  }

  def fresh(name: String, argSorts: Seq[Sort], resultSort: Sort): Fun = {
    val id = identifierFactory.fresh(name)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)

    emit(termConverter.convert(decl))

    fun
  }

  def declare(decl: Decl): Unit = {
    val str = termConverter.convert(decl)
    if (debugMode)
      allDecls = allDecls :+ decl
    emit(str)
  }

  def getAllDecls(): Seq[Decl] = allDecls

  protected def setTimeout(timeout: Option[Int]): Unit = {
    val effectiveTimeout = timeout.getOrElse(Verifier.config.proverTimeout)

    if (lastTimeout != effectiveTimeout) {
      lastTimeout = effectiveTimeout
      applyTimeout()
    }
  }

  /* Sets the per-query limit that corresponds to lastTimeout (see also Cvc5ProverStdIO.setTimeout). The resource
   * limit is set in either case since it is also used to interrupt queries, after which it must be lifted again. */
  private def applyTimeout(): Unit = {
    val effectiveTimeout = Math.max(0, lastTimeout).toLong

    if (!Verifier.config.proverEnableTimeBounds()) {
      setSolverOption(Cvc5ProverAPI.resourceLimitOption, (effectiveTimeout * Verifier.config.cvc5ResourcesPerMillisecond()).toString)
    } else {
      setSolverOption(Cvc5ProverAPI.resourceLimitOption, "0")
      setSolverOption(Cvc5ProverAPI.timeLimitOption, effectiveTimeout.toString)
    }
  }

  private def setSolverOption(name: String, value: String): Unit = {
    logToFile(s"(set-option :$name $value)")
    solver.setOption(name, value)
  }

  protected def logToFile(str: String): Unit = {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }

  lazy val name: String = Cvc5ProverAPI.name

  lazy val minVersion: Version = Cvc5ProverAPI.minVersion

  lazy val maxVersion: Option[Version] = Cvc5ProverAPI.maxVersion

  lazy val staticPreamble: String = Cvc5ProverAPI.staticPreamble

  lazy val randomizeSeedsOptions: Seq[String] = Cvc5ProverAPI.randomizeSeedsOptions
}
