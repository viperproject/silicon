// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.decider

import java.io._
import java.nio.file.Path
import java.util.concurrent.TimeUnit

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Result, Sat, Unknown, Unsat}
import viper.silicon.reporting.{ExternalToolError, ProverInteractionFailed}
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.verifier.{DefaultDependency => SilDefaultDependency}
import viper.silicon.{Config, Map, toMap}
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage, Reporter, QuantifierInstantiationsMessage}
import viper.silver.verifier.Model

import scala.collection.mutable

abstract class ProverStdIO(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory,
                    reporter: Reporter)
    extends Prover
       with LazyLogging {

  /* protected */ var pushPopScopeDepth = 0
  protected var lastTimeout: Int = -1
  protected var logfileWriter: PrintWriter = _
  protected var prover: Process = _
  protected var proverShutdownHook: Thread = _
  protected var input: BufferedReader = _
  protected var output: PrintWriter = _

  var proverPath: Path = _
  var lastReasonUnknown : String = _
  var lastModel : String = _

  def exeEnvironmentalVariable: String
  def dependencies: Seq[SilDefaultDependency]
  def startUpArgs: Seq[String]

  protected def setTimeout(timeout: Option[Int]): Unit
  protected def getProverPath: Path

  @inline
  private def readLineFromInput(): String = {
    val line = input.readLine()

    if (line == null) {
      throw ProverInteractionFailed(uniqueId, s"Interaction with prover yielded null. This might indicate that the prover crashed.")
    }

    line
  }

  def version(): Version = {
    val versionPattern = """\(?\s*:version\s+"(.*?)(?:\s*-.*?)?"\)?""".r
    var line = ""

    writeLine("(get-info :version)")

    line = readLineFromInput()
    comment(line)

    line match {
      case versionPattern(v) => Version(v)
      case _ => throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover while getting version: $line")
    }
  }

  def start(): Unit = {
    // Calling `start()` multiple times in a row would leak memory and prover processes.
    if (proverShutdownHook != null) {
      throw new AssertionError("stop() should be called between any pair of start() calls")
    }
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = if (!Verifier.config.enableTempDirectory()) null else viper.silver.utility.Common.PrintWriter(Verifier.config.proverLogFile(uniqueId).toFile)
    proverPath = getProverPath
    prover = createProverInstance()
    input = new BufferedReader(new InputStreamReader(prover.getInputStream))
    output = new PrintWriter(new BufferedWriter(new OutputStreamWriter(prover.getOutputStream)), true)
    // Register a shutdown hook to stop prover when the JVM gracefully terminates.
    // Note that if the JVM abruptly terminates (e.g. because of a SIGKILL)
    // this hook will not be executed and the prover process will be left running.
    proverShutdownHook = new Thread {
      override def run(): Unit = {
        if (prover.isAlive) {
          prover.destroyForcibly()
        }
      }
    }
    Runtime.getRuntime.addShutdownHook(proverShutdownHook)
  }

  protected def createProverInstance(): Process = {
    // One can pass some options. This allows to check whether they have been received.
    val msg = s"Starting prover at location '$proverPath'"
    reporter report ConfigurationConfirmation(msg)
    logger debug msg

    val proverFile = proverPath.toFile

    if (!proverFile.isFile)
      throw ExternalToolError("Prover", s"Cannot run prover at location '$proverFile': not a file.")

    if (!proverFile.canExecute)
      throw ExternalToolError("Prover", s"Cannot run prover at location '$proverFile': file is not executable.")

    val userProvidedArgs: Array[String] = Verifier.config.proverArgs match {
      case None =>
        Array()

      case Some(args) =>
        // One can pass some options. This allows to check whether they have been received.
        val msg = s"Additional command-line arguments are $args"
        reporter report ConfigurationConfirmation(msg)
        logger debug msg
        args.split(' ').map(_.trim)
    }

    val builder = new ProcessBuilder(proverPath.toFile.getPath +: startUpArgs ++: userProvidedArgs :_*)
    builder.redirectErrorStream(true)

    builder.start()
  }

  def reset(): Unit = {
    stop()
    start()
  }

  /* The statement input.close() does not always terminate (e.g. if there is data left to be read).
   * It therefore makes sense to first kill the prover process because then the channel is closed from
   * the other side first, resulting in the close() method to terminate.
   */
  def stop(): Unit = {
    this.synchronized {
      if (logfileWriter != null) {
        logfileWriter.flush()
      }
      if (output != null) {
        output.flush()
      }
      if (prover != null) {
        prover.destroyForcibly()
        prover.waitFor(10, TimeUnit.SECONDS) /* Makes the current thread wait until the process has been shut down */
      }

      if (logfileWriter != null) {
        logfileWriter.close()
      }
      if (input != null) {
        input.close()
      }
      if (output != null) {
        output.close()
      }

      if (proverShutdownHook != null) {
        // Deregister the shutdown hook, otherwise the prover process that has been stopped cannot be garbage collected.
        // Explanation: https://blog.creekorful.org/2020/03/classloader-and-memory-leaks/
        // Bug report: https://github.com/viperproject/silicon/issues/579
        Runtime.getRuntime.removeShutdownHook(proverShutdownHook)
        proverShutdownHook = null
      }
    }
  }

  def push(n: Int = 1, timeout: Option[Int] = None): Unit = {
    setTimeout(timeout)
    pushPopScopeDepth += n
    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + pushPopScopeDepth
    writeLine(cmd)
    readSuccess()
  }

  def pop(n: Int = 1): Unit = {
    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + pushPopScopeDepth
    pushPopScopeDepth -= n
    writeLine(cmd)
    readSuccess()
  }

  def emit(content: String): Unit = {
    writeLine(content)
    readSuccess()
  }

//  private val quantificationLogger = bookkeeper.logfiles("quantification-problems")

  def assume(term: Term): Unit = {
//    /* Detect certain simple problems with quantifiers.
//     * Note that the current checks don't take in account whether or not a
//     * quantification occurs in positive or negative position.
//     */
//    term.deepCollect{case q: Quantification => q}.foreach(q => {
//      val problems = QuantifierSupporter.detectQuantificationProblems(q)
//
//      if (problems.nonEmpty) {
//        quantificationLogger.println(s"\n\n${q.toString(true)}")
//        quantificationLogger.println("Problems:")
//        problems.foreach(p => quantificationLogger.println(s"  $p"))
//      }
//    })

    assume(termConverter.convert(term))
  }

  def assume(term: String): Unit = {
//    bookkeeper.assumptionCounter += 1

    writeLine("(assert " + term + ")")
    readSuccess()
  }

  def assert(goal: Term, timeout: Option[Int] = None): Boolean =
    assert(termConverter.convert(goal), timeout)

  def assert(goal: String, timeout: Option[Int]): Boolean = {
//    bookkeeper.assertionCounter += 1

    val (result, duration) = Verifier.config.assertionMode() match {
      case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal, timeout)
      case Config.AssertionMode.PushPop => assertUsingPushPop(goal, timeout)
    }

    comment(s"${viper.silver.reporter.format.formatMillisReadably(duration)}")
    comment("(get-info :all-statistics)")

    result
  }

  protected def assertUsingPushPop(goal: String, timeout: Option[Int]): (Boolean, Long) = {
    push()
    setTimeout(timeout)

    writeLine("(assert (not " + goal + "))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine("(check-sat)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    if (!result) {
      retrieveAndSaveModel()
      retrieveReasonUnknown()
    }

    pop()

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
    writeLine("(check-sat)")
    readLine()
  }

  protected def retrieveAndSaveModel(): Unit = {
    if (Verifier.config.counterexample.toOption.isDefined) {
      writeLine("(get-model)")

      var model = readModel("\n").trim()
      if (model.startsWith("\"")) {
        model = model.replaceAll("\"", "")
      }
      lastModel = model
    }
  }

  protected def retrieveReasonUnknown(): Unit = {
    if (Verifier.config.reportReasonUnknown()) {
      writeLine("(get-info :reason-unknown)")
      var result = readLine()
      if (result.startsWith("(:reason-unknown \""))
        result = result.substring(18, result.length - 2)
      lastReasonUnknown = result
    }
  }

  override def hasModel(): Boolean = {
    lastModel != null
  }

  override def isModelValid(): Boolean = {
    lastModel != null && !lastModel.contains("model is not available")
  }

  protected def assertUsingSoftConstraints(goal: String, timeout: Option[Int]): (Boolean, Long) = {
    setTimeout(timeout)

    val guard = fresh("grd", Nil, sorts.Bool)
    val guardApp = App(guard, Nil)

    writeLine(s"(assert (=> $guardApp (not $goal)))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine(s"(check-sat $guardApp)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    if (!result) {
      retrieveAndSaveModel()
    }

    (result, endTime - startTime)
  }

  def check(timeout: Option[Int] = None): Result = {
    setTimeout(timeout)

    writeLine("(check-sat)")

    readLine() match {
      case "sat" => Sat
      case "unsat" => Unsat
      case "unknown" => Unknown
    }
  }

  def statistics(): Map[String, String] = {
    var repeat = true
    var line = ""
    var stats = scala.collection.immutable.SortedMap[String, String]()
    val entryPattern = """\(?\s*:([A-za-z\-]+)\s+((?:\d+\.)?\d+)\)?""".r

    writeLine("(get-info :all-statistics)")

    do {
      line = readLineFromInput()
      comment(line)

      /* Check that the first line starts with "(:". */
      if (line.isEmpty && !line.startsWith("(:"))
        throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover while reading statistics: $line")

      line match {
        case entryPattern(entryName, entryNumber) =>
          stats = stats + (entryName -> entryNumber)
        case _ =>
      }

      repeat = !line.endsWith(")")
    } while (repeat)

    toMap(stats)
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
    emit(str)
  }

//  def resetAssertionCounter() { bookkeeper.assertionCounter = 0 }
//  def resetAssumptionCounter() { bookkeeper.assumptionCounter = 0 }

//  def resetCounters() {
//    resetAssertionCounter()
//    resetAssumptionCounter()
//  }

  /* TODO: Handle multi-line output, e.g. multiple error messages. */

  protected def readSuccess(): Unit = {
    val answer = readLine()

    if (answer != "success")
      throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover. Expected 'success' but found: $answer")
  }

  protected def readUnsat(): Boolean = readLine() match {
    case "unsat" => true
    case "sat" => false
    case "unknown" => false

    case result =>
      throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover while trying to refute an assertion: $result")
  }

  protected def readModel(separator: String): String = {
    try {
      var endFound = false
      val result = new mutable.StringBuilder
      var firstTime = true
      while (!endFound) {
        val nextLine = readLineFromInput()
        if (nextLine.trim().endsWith("\"") || (firstTime && !nextLine.startsWith("\""))) {
          endFound = true
        }
        result.append(separator).append(nextLine)
        firstTime = false
      }
      result.result()
    } catch {
      case e: Exception =>
        println("Error reading model: " + e)
        ""
    }
  }

  protected def readLine(): String = {
    var repeat = true
    var result = ""

    while (repeat) {
      result = readLineFromInput()
      if (result.toLowerCase != "success") comment(result)

      val warning = result.startsWith("WARNING")
      if (warning) {
        val msg = s"Prover warning: $result"
        reporter report InternalWarningMessage(msg)
        logger warn msg
      }

      // When `smt.qi.profile` is `true`, Z3 periodically reports the quantifier instantiations using the format
      // `[quantifier_instances] "<quantifier_id>" : <instances> : <maximum generation> : <maximum cost>`.
      // See: https://github.com/Z3Prover/z3/issues/4522
      val qiProfile = result.startsWith("[quantifier_instances]")
      if (qiProfile) {
        val qi_info = result.stripPrefix("[quantifier_instances]").split(":").map(_.trim)
        if (qi_info.length != 4) {
          val msg = s"Invalid quantifier instances line from prover: $result"
          reporter report InternalWarningMessage(msg)
          logger warn msg
        } else {
          reporter report QuantifierInstantiationsMessage(qi_info(0), qi_info(1).toInt, qi_info(2).toInt, qi_info(3).toInt)
          logger info result
        }
      }

      repeat = warning || qiProfile
    }

    result
  }

  protected def logToFile(str: String): Unit = {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }

  protected def writeLine(out: String): Unit = {
    logToFile(out)
    output.println(out)
  }

  override def getModel(): Model = Model(lastModel)

  override def getReasonUnknown(): String = lastReasonUnknown

  override def clearLastAssert(): Unit = {
    lastReasonUnknown = null
    lastModel = null
  }
}
