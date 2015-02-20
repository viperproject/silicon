/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package decider

import java.io.{PrintWriter, BufferedWriter, InputStreamReader, BufferedReader, OutputStreamWriter}
import java.nio.file.{Path, Paths}
import com.weiglewilczek.slf4s.Logging
import org.apache.commons.io.FileUtils
import interfaces.decider.{Prover, Sat, Unsat, Unknown}
import state.terms._
import reporting.{Bookkeeper, Z3InteractionFailed}

/* TODO: Pass a logger, don't open an own file to log to. */
class Z3ProverStdIO(config: Config, bookkeeper: Bookkeeper) extends Prover with Logging {
  val termConverter = new TermToSMTLib2Converter()
  import termConverter._

  private var scopeCounter = 0
  private val scopeLabels = new MMap[String, MStack[Int]]()
  private var isLoggingCommentsEnabled: Boolean = true
  private var logFile: PrintWriter = _
  private var z3: Process = _
  private var input: BufferedReader = _
  private var output: PrintWriter = _
  /* private */ var z3Path: Path = _
  private var logPath: Path = _

  def z3Version() = {
    val versionPattern = """\(?\s*:version\s+"(.*?)"\)?""".r
    var line = ""

    writeLine("(get-info :version)")

    line = input.readLine()
    logComment(line)

    line match {
      case versionPattern(v) => v
      case _ => throw new Z3InteractionFailed(s"Unexpected output of Z3 while getting version: $line")
    }
  }

  def start() {
    logPath = config.z3LogFile
    logFile = silver.utility.Common.PrintWriter(logPath.toFile)
    z3Path = Paths.get(config.z3Exe)
    z3 = createZ3Instance()
    input = new BufferedReader(new InputStreamReader(z3.getInputStream))
    output = new PrintWriter(new BufferedWriter(new OutputStreamWriter(z3.getOutputStream)), true)
  }

  /* Note: This is just a hack to get the input file name to the prover */
  def proverRunStarts() {
    logComment(s"Input file is ${config.inputFile.getOrElse("<unknown>")}")
  }

  private def createZ3Instance() = {
    logger.info(s"Starting Z3 at $z3Path")

    val builder = new ProcessBuilder(z3Path.toFile.getPath, "-smt2", "-in")
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
    scopeLabels.clear()
    scopeCounter = 0
    counter.reset()
    start()
  }

  def stop() {
    this.synchronized {
      logFile.flush()
      output.flush()

      logFile.close()
      input.close()
      output.close()

      z3.destroy()
//      z3.waitFor() /* Makes the current thread wait until the process has been shut down */

      val currentLogPath = config.z3LogFile
      if (logPath != currentLogPath) {
        /* This is a hack to make it possible to name the SMTLIB logfile after
         * the input file that was verified. Currently, Silicon starts Z3 before
         * the input file name is known, which is partially due to our crappy
         * and complicated way of how command-line arguments are parsed and
         * how Silver programs are passed to verifiers.
         */

        FileUtils.moveFile(logPath.toFile, currentLogPath.toFile)
      }
    }
  }

  def  push(label: String) {
    val stack =
      scopeLabels.getOrElse(
        label,
        {val s = new MStack[Int](); scopeLabels(label) = s; s})

    stack.push(scopeCounter)
    push()
  }

  def  pop(label: String) {
    val stack = scopeLabels(label)
    val n = scopeCounter - stack.head
    stack.pop()
    pop(n)
  }

  def push(n: Int = 1) {
    scopeCounter += n
    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + scopeCounter
    writeLine(cmd)
    readSuccess()
  }

  def pop(n: Int = 1) {
    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + scopeCounter
    scopeCounter -= n
    writeLine(cmd)
    readSuccess()
  }

  def write(content: String) {
    writeLine(content)
    readSuccess()
  }

  def assume(term: Term) = assume(convert(term))

  def assume(term: String) {
    bookkeeper.assumptionCounter += 1

    writeLine("(assert " + term + ")")
    readSuccess()
  }

  def assert(goal: Term) = assert(convert(goal))

  def assert(goal: String) = {
    bookkeeper.assertionCounter += 1

    push()
    writeLine("(assert (not " + goal + "))")
    readSuccess()
    val startTime = System.currentTimeMillis()
    writeLine("(check-sat)")
    val r = readUnsat()
    val endTime = System.currentTimeMillis()
    logComment(s"${common.format.formatMillisReadably(endTime - startTime)}")
    pop()

    r
  }

  def check() = {
    writeLine("(check-sat)")

    readLine() match {
      case "sat" => Sat
      case "unsat" => Unsat
      case "unknown" => Unknown
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
      logComment(line)

      /* Check that the first line starts with "(:". */
      if (line.isEmpty && !line.startsWith("(:"))
        throw new Z3InteractionFailed(s"Unexpected output of Z3 while reading statistics: $line")

      line match {
        case entryPattern(entryName, entryNumber) =>
          stats = stats + (entryName -> entryNumber)
        case _ =>
      }

      repeat = !line.endsWith(")")
    } while (repeat)

    toMap(stats)
  }

  def enableLoggingComments(enabled: Boolean) = isLoggingCommentsEnabled = enabled

  def logComment(str: String) =
    if (isLoggingCommentsEnabled) {
      val sanitisedStr =
        str.replaceAll("\r", "")
           .replaceAll("\n", "\n; ")

      log("; " + sanitisedStr)
    }

  private def freshId(prefix: String) = prefix + "@" + counter.next()

  /* TODO: Could we decouple fresh from Var, e.g. return the used freshId, without
   *       losing conciseness at call-site?
   *       It is also slightly fishy that fresh returns a Var although it
   *       declared a new Function.
   */
  def fresh(idPrefix: String, sort: Sort) = {
    val id = freshId(idPrefix)

    val decl = sort match {
      case arrow: sorts.Arrow => FunctionDecl(Function(id, arrow))
      case _ => VarDecl(Var(id, sort))
    }

    write(convert(decl))

    Var(id, sort)
  }

  def sanitizeSymbol(symbol: String) = termConverter.sanitizeSymbol(symbol)

  def declare(decl: Decl) {
    val str = convert(decl)
    write(str)
  }

  def resetAssertionCounter() { bookkeeper.assertionCounter = 0 }
  def resetAssumptionCounter() { bookkeeper.assumptionCounter = 0 }

  def resetCounters() {
    resetAssertionCounter()
    resetAssumptionCounter()
  }

  /* TODO: Handle multi-line output, e.g. multiple error messages. */

  private def readSuccess() {
    val answer = readLine()

    if (answer != "success")
      throw new Z3InteractionFailed(s"Unexpected output of Z3. Expected 'success' but found: $answer")
  }

  private def readUnsat(): Boolean = readLine() match {
    case "unsat" => true
    case "sat" => false
    case "unknown" => false

    case result =>
      throw new Z3InteractionFailed(s"Unexpected output of Z3 while trying to refute an assertion: $result")
  }

  private def readLine(): String = {
    var repeat = true
    var result = ""

    while (repeat) {
      result = input.readLine()
      if (result.toLowerCase != "success") logComment(result)

      repeat = result.startsWith("WARNING")
    }

    result
  }

  private def log(str: String) {
    logFile.println(str)
  }

  private def writeLine(out: String) = {
    log(out)
    output.println(out)
  }

  private object counter {
    private var value = 0

    def next() = {
      value = value + 1
      value
    }

    def reset() {
      value = 0
    }
  }
}
