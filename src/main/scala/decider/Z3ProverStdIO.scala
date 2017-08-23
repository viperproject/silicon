/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.decider

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.{Path, Paths}
import java.util.concurrent.TimeUnit
import com.typesafe.scalalogging.LazyLogging
import viper.silicon.{Config, Map, toMap}
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Sat, Unknown, Unsat}
import viper.silicon.reporting.{ExternalToolError, Z3InteractionFailed}
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier

class Z3ProverStdIO(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory)
    extends Prover
       with LazyLogging {

  private var pushPopScopeDepth = 0
  private var lastTimeout: Int = -1
  private var logfileWriter: PrintWriter = _
  private var z3: Process = _
  private var input: BufferedReader = _
  private var output: PrintWriter = _
  /* private */ var z3Path: Path = _

  def z3Version(): Version = {
    val versionPattern = """\(?\s*:version\s+"(.*?)"\)?""".r
    var line = ""

    writeLine("(get-info :version)")

    line = input.readLine()
    comment(line)

    line match {
      case versionPattern(v) => Version(v)
      case _ => throw Z3InteractionFailed(uniqueId, s"Unexpected output of Z3 while getting version: $line")
    }
  }

  def start() {
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = viper.silver.utility.Common.PrintWriter(Verifier.config.z3LogFile(uniqueId).toFile)
    z3Path = Paths.get(Verifier.config.z3Exe)
    z3 = createZ3Instance()
    input = new BufferedReader(new InputStreamReader(z3.getInputStream))
    output = new PrintWriter(new BufferedWriter(new OutputStreamWriter(z3.getOutputStream)), true)
  }

  private def createZ3Instance() = {
    logger.debug(s"Starting Z3 at location '$z3Path'")

    val z3File = z3Path.toFile

    if (!z3File.isFile)
      throw ExternalToolError("Z3", s"Cannot run Z3 at location '$z3File': not a file.")

    if (!z3File.canExecute)
      throw ExternalToolError("Z3", s"Cannot run Z3 at location '$z3File': file is not executable.")

    val userProvidedZ3Args: Array[String] = Verifier.config.z3Args.toOption match {
      case None =>
        Array()

      case Some(args) =>
        logger.debug(s"Additional command-line arguments are $args")
        args.split(' ').map(_.trim)
    }

    val builder = new ProcessBuilder(z3Path.toFile.getPath +: "-smt2" +: "-in" +: userProvidedZ3Args :_*)
    builder.redirectErrorStream(true)

    val process = builder.start()

    Runtime.getRuntime.addShutdownHook(new Thread {
      override def run() {
        process.destroy()
      }
    })

    process
  }

  def reset() {
    stop()
    start()
  }

  /* The statement input.close() does not always terminate (e.g. if there is data left to be read).
   * It therefore makes sense to first kill the Z3 process because then the channel is closed from
   * the other side first, resulting in the close() method to terminate.
   */
  def stop() {
    this.synchronized {
      if (logfileWriter != null) {
        logfileWriter.flush()
      }
      if (output != null) {
        output.flush()
      }
      if (z3 != null) {
        z3.destroyForcibly()
        z3.waitFor(10, TimeUnit.SECONDS) /* Makes the current thread wait until the process has been shut down */
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
    }
  }

  def push(n: Int = 1) {
    pushPopScopeDepth += n
    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + pushPopScopeDepth
    writeLine(cmd)
    readSuccess()
  }

  def pop(n: Int = 1) {
    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + pushPopScopeDepth
    pushPopScopeDepth -= n
    writeLine(cmd)
    readSuccess()
  }

  def emit(content: String) {
    writeLine(content)
    readSuccess()
  }

//  private val quantificationLogger = bookkeeper.logfiles("quantification-problems")

  def assume(term: Term) = {
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

  def assume(term: String) {
//    bookkeeper.assumptionCounter += 1

    writeLine("(assert " + term + ")")
    readSuccess()
  }

  def assert(goal: Term, timeout: Option[Int] = None) =
    assert(termConverter.convert(goal), timeout)

  def assert(goal: String, timeout: Option[Int]) = {
//    bookkeeper.assertionCounter += 1

    setTimeout(timeout)

    val (result, duration) = Verifier.config.assertionMode() match {
      case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal)
      case Config.AssertionMode.PushPop => assertUsingPushPop(goal)
    }

    comment(s"${viper.silicon.common.format.formatMillisReadably(duration)}")
    comment("(get-info :all-statistics)")

    result
  }

  private def assertUsingPushPop(goal: String): (Boolean, Long) = {
    push()

    writeLine("(assert (not " + goal + "))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine("(check-sat)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    if (!result) {
      getModel()
    }

    pop()

    (result, endTime - startTime)
  }

  def saturate(data: Option[Config.Z3StateSaturationTimeout]): Unit = {
    data match {
      case Some(Config.Z3StateSaturationTimeout(timeout, comment)) => saturate(timeout, comment)
      case None => /* Don't do anything */
    }
  }

  def saturate(timeout: Int, comment: String): Unit = {
    this.comment(s"State saturation: $comment")
    setTimeout(Some(timeout))
    writeLine("(check-sat)")
    readLine()
  }

  private def getModel(): Unit = {
    if (Verifier.config.ideModeAdvanced()) {
      writeLine("(get-model)")
      val model = readModel().trim()
      println(model + "\r\n")
    }
  }

  private def assertUsingSoftConstraints(goal: String): (Boolean, Long) = {
    val guard = fresh("grd", Nil, sorts.Bool)

    writeLine(s"(assert (implies $guard (not $goal)))")
    readSuccess()

    val startTime = System.currentTimeMillis()
    writeLine(s"(check-sat $guard)")
    val result = readUnsat()
    val endTime = System.currentTimeMillis()

    if (!result) {
      getModel()
    }

    (result, endTime - startTime)
  }

  def check(timeout: Option[Int] = None) = {
    setTimeout(timeout)

    writeLine("(check-sat)")

    readLine() match {
      case "sat" => Sat
      case "unsat" => Unsat
      case "unknown" => Unknown
    }
  }

  private def setTimeout(timeout: Option[Int]) {
    val effectiveTimeout = timeout.getOrElse(Verifier.config.z3Timeout)

    /* [2015-07-27 Malte] Setting the timeout unnecessarily often seems to
     * worsen performance, if only a bit. For the current test suite of
     * 199 Silver files, the total verification time increased from 60s
     * to 70s if 'set-option' is emitted every time.
     */
    if (lastTimeout != effectiveTimeout) {
      lastTimeout = effectiveTimeout

      writeLine(s"(set-option :timeout $effectiveTimeout)")
      readSuccess()
    }
  }

  def statistics(): Map[String, String]= {
    var repeat = true
    var line = ""
    var stats = scala.collection.immutable.SortedMap[String, String]()
    val entryPattern = """\(?\s*:([A-za-z\-]+)\s+((?:\d+\.)?\d+)\)?""".r

    writeLine("(get-info :all-statistics)")

    do {
      line = input.readLine()
      comment(line)

      /* Check that the first line starts with "(:". */
      if (line.isEmpty && !line.startsWith("(:"))
        throw Z3InteractionFailed(uniqueId, s"Unexpected output of Z3 while reading statistics: $line")

      line match {
        case entryPattern(entryName, entryNumber) =>
          stats = stats + (entryName -> entryNumber)
        case _ =>
      }

      repeat = !line.endsWith(")")
    } while (repeat)

    toMap(stats)
  }

  def comment(str: String) = {
    val sanitisedStr =
      str.replaceAll("\r", "")
         .replaceAll("\n", "\n; ")

    logToFile("; " + sanitisedStr)
  }

  def fresh(name: String, argSorts: Seq[Sort], resultSort: Sort) = {
    val id = identifierFactory.fresh(name)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)

    emit(termConverter.convert(decl))

    fun
  }

  def declare(decl: Decl) {
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

  private def readSuccess() {
    val answer = readLine()

    if (answer != "success")
      throw Z3InteractionFailed(uniqueId, s"Unexpected output of Z3. Expected 'success' but found: $answer")
  }

  private def readUnsat(): Boolean = readLine() match {
    case "unsat" => true
    case "sat" => false
    case "unknown" => false

    case result =>
      throw Z3InteractionFailed(uniqueId, s"Unexpected output of Z3 while trying to refute an assertion: $result")
  }

  private def readModel(): String = {
    try {
      var endFound = false
      var result = ""
      var firstTime = true
      while (!endFound) {
        val nextLine = input.readLine()
        if (nextLine.trim().endsWith("\"") || (firstTime && !nextLine.startsWith("\""))) {
          endFound = true
        }
        result = result + " " + nextLine
        firstTime = false
      }
      result
    } catch {
      case e: Exception =>
        println("Error reading model: " + e)
        ""
    }
  }

  private def readLine(): String = {
    var repeat = true
    var result = ""

    while (repeat) {
      result = input.readLine()
      if (result.toLowerCase != "success") comment(result)

      val warning = result.startsWith("WARNING")
      if (warning) logger.warn(s"Z3 warning: $result")

      repeat = warning
    }

    result
  }

  private def logToFile(str: String) {
    logfileWriter.println(str)
  }

  private def writeLine(out: String) = {
    logToFile(out)
    output.println(out)
  }
}
