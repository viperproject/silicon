// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.common.config.Version
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.interfaces.decider.{Prover, Result, Sat, Unknown, Unsat}
import viper.silicon.reporting.{ExternalToolError, ProverInteractionFailed}
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms.{Decl, Fun, FunctionDecl, MacroDecl, Sort, SortDecl, SortWrapperDecl, Term, sorts}
import viper.silicon.{Config, Map, toMap}
import viper.silicon.verifier.Verifier
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage, Reporter}
import viper.silver.verifier.{DefaultDependency => SilDefaultDependency}

import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.{Path, Paths}
import java.util.concurrent.TimeUnit
import scala.collection.mutable
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_ast_print_mode

import scala.jdk.CollectionConverters
import scala.jdk.CollectionConverters.MapHasAsJava


object Z3ProverAPI {
  val name = "Z3-API"
  val minVersion = Version("4.8.6.0")
  val maxVersion = Some(Version("4.8.6.0")) /* X.Y.Z if that is the *last supported* version */
  val exeEnvironmentalVariable = "Z3_EXE"
  val dependencies = Seq(SilDefaultDependency("Z3", minVersion.version, "https://github.com/Z3Prover/z3"))
  val staticPreamble = "/z3config.smt2"
  val startUpArgs = Seq("-smt2", "-in")
  val randomizeSeedsOptions = Seq("sat.random_seed", "nlsat.seed", "fp.spacer.random_seed", "smt.random_seed", "sls.random_seed")
/*
(set-option :smt.arith.random_initial_value true) ; Boogie: true
(set-option :smt.random_seed 0)
(set-option :sls.random_offset true)
(set-option :sls.random_seed 0)
(set-option :sls.restart_init false)
(set-option :sls.walksat_ucb true)

 */
  val initialOptions = Map("auto_config" -> "false", "type_check" -> "true")
  val boolParams = Map(
    "smt.delay_units" -> true,
    "nnf.sk_hack" -> true,
  //  "type_check" -> true,
 //   "smt.bv_reflect" -> true,
  //  "global-decls" -> true,
    "smt.mbqi" -> false,
 //   "model.v2" -> true,
    "nlsat.randomize" -> true,
    "nlsat.shuffle_vars" -> false,
    "smt.arith.random_initial_value" -> true,
 //   "sls.random_offset" -> true
 //   "sls.restart_init" -> false,
  //  "sls.walksat_ucb" -> true
  )
  val intParams = Map("smt.restart_strategy" -> 0,
    "smt.case_split" -> 3,
    "smt.delay_units_threshold" -> 16,
    "smt.qi.max_multi_patterns" -> 1000,
    "smt.phase_selection" -> 0,
    "sat.random_seed" -> 0,
    "nlsat.seed" -> 0,
 //   "fp.spacer.order_children" -> 0,
 //   "fp.spacer.random_seed" -> 0
    "random_seed" -> 0,
 //   "sls.random_seed" -> 0
  )
  val stringParams = Map(
    //"smt.qi.cost" -> "(+ weight generation)", // cannot set this for some reason, but this is the default value anyway.
    "sat.phase" -> "caching"
  )
  val doubleParams = Map(
    "smt.restart_factor" -> 1.5,
    "smt.qi.eager_threshold" -> 100.0,
  )
}

/*

TODO: missing randomness-related options
 */


class Z3ProverAPI(uniqueId: String,
                  termConverter: TermToZ3APIConverter,
                  identifierFactory: IdentifierFactory,
                  reporter: Reporter)
    extends Prover
      with LazyLogging
{

  protected var pushPopScopeDepth = 0
  protected var lastTimeout: Int = -1
  protected var logfileWriter: PrintWriter = _
  protected var prover: Solver = _
  protected var ctx: Context = _

  var proverPath: Path = _
  var lastModel : String = _

  var emittedPreambleString = mutable.Queue[String]()
  var preamblePhaseOver = false
  var preambleAssumes = mutable.LinkedHashSet[BoolExpr]()
  val emittedSorts = mutable.LinkedHashSet[com.microsoft.z3.Sort]()
  val emittedSortSymbols = mutable.LinkedHashSet[Symbol]()
  val emittedFuncs = mutable.LinkedHashSet[FuncDecl]()
  val emittedFuncSymbols = mutable.Queue[Symbol]()

  val expandMacros = true



  def version(): Version = {
    val versString = com.microsoft.z3.Version.getFullVersion
    if (!versString.startsWith("Z3 "))
      sys.error("unexpected version string")
    Version(versString.substring(3))
  }

  def start(): Unit = {
//    // Calling `start()` multiple times in a row would leak memory and prover processes.
//    if (proverShutdownHook != null) {
//      throw new AssertionError("stop() should be called between any pair of start() calls")
//    }
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = if (Verifier.config.disableTempDirectory()) null else viper.silver.utility.Common.PrintWriter(Verifier.config.proverLogFile(uniqueId).toFile)
    //proverPath = getProverPath
    ctx = new Context(Z3ProverAPI.initialOptions.asJava)
    val params = ctx.mkParams()
    Z3ProverAPI.boolParams.foreach{
      case (k, v) => params.add(k, v)
    }
    Z3ProverAPI.intParams.foreach{
      case (k, v) => params.add(k, v)
    }
    Z3ProverAPI.doubleParams.foreach{
      case (k, v) => params.add(k, v)
    }
    Z3ProverAPI.stringParams.foreach{
      case (k, v) => params.add(k, v)
    }
    prover = ctx.mkSolver()
    prover.setParameters(params)
    termConverter.start()
    termConverter.ctx = ctx
    emittedPreambleString.clear()
    preamblePhaseOver = false
    emittedFuncs.clear()
    emittedSorts.clear()
    emittedFuncSymbols.clear()
    emittedSortSymbols.clear()
  }

//  protected def createProverInstance(): Process = {
//    // One can pass some options. This allows to check whether they have been received.
//    val msg = s"Starting prover at location '$proverPath'"
//    reporter report ConfigurationConfirmation(msg)
//    logger debug msg
//
//    val proverFile = proverPath.toFile
//
//    if (!proverFile.isFile)
//      throw ExternalToolError("Prover", s"Cannot run prover at location '$proverFile': not a file.")
//
//    if (!proverFile.canExecute)
//      throw ExternalToolError("Prover", s"Cannot run prover at location '$proverFile': file is not executable.")
//
//    val userProvidedArgs: Array[String] = Verifier.config.proverArgs match {
//      case None =>
//        Array()
//
//      case Some(args) =>
//        // One can pass some options. This allows to check whether they have been received.
//        val msg = s"Additional command-line arguments are $args"
//        reporter report ConfigurationConfirmation(msg)
//        logger debug msg
//        args.split(' ').map(_.trim)
//    }
//
//    val builder = new ProcessBuilder(proverPath.toFile.getPath +: startUpArgs ++: userProvidedArgs :_*)
//    builder.redirectErrorStream(true)
//
//    builder.start()
//  }

  def reset(): Unit = {
    stop()
    termConverter.reset()
    start()
  }

  /* The statement input.close() does not always terminate (e.g. if there is data left to be read).
   * It therefore makes sense to first kill the prover process because then the channel is closed from
   * the other side first, resulting in the close() method to terminate.
   */
  def stop(): Unit = {
//    this.synchronized {
//      if (logfileWriter != null) {
//        logfileWriter.flush()
//      }
//      if (output != null) {
//        output.flush()
//      }
//      if (prover != null) {
//        prover.destroyForcibly()
//        prover.waitFor(10, TimeUnit.SECONDS) /* Makes the current thread wait until the process has been shut down */
//      }
//
//      if (logfileWriter != null) {
//        logfileWriter.close()
//      }
//      if (input != null) {
//        input.close()
//      }
//      if (output != null) {
//        output.close()
//      }
//
//      if (proverShutdownHook != null) {
//        // Deregister the shutdown hook, otherwise the prover process that has been stopped cannot be garbage collected.
//        // Explanation: https://blog.creekorful.org/2020/03/classloader-and-memory-leaks/
//        // Bug report: https://github.com/viperproject/silicon/issues/579
//        Runtime.getRuntime.removeShutdownHook(proverShutdownHook)
//        proverShutdownHook = null
//      }
//    }
    if (ctx != null){
      ctx.close()
      ctx = null
      emittedPreambleString.clear()
      preamblePhaseOver = false
      emittedFuncs.clear()
      emittedSorts.clear()
      emittedFuncSymbols.clear()
      emittedSortSymbols.clear()
    }
  }

  def push(n: Int = 1): Unit = {
    endPreamblePhase()
    pushPopScopeDepth += n
//    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + pushPopScopeDepth
//    writeLine(cmd)
//    readSuccess()
    if (n != 1)
      sys.error("wtf")
    prover.push()
  }

  def pop(n: Int = 1): Unit = {
    endPreamblePhase()
    prover.pop(n)
//    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + pushPopScopeDepth
    pushPopScopeDepth -= n
//    writeLine(cmd)
//    readSuccess()
  }

  def emit(content: String): Unit = {
    if (preamblePhaseOver) {
      sys.error("emitting phase over")
    }
    emittedPreambleString.append(content)
  }

  override def emit(contents: Iterable[String]): Unit = {
    if (preamblePhaseOver) {
      sys.error("emitting phase over")
    }
    emittedPreambleString.appendAll(contents)
  }

  override def emitSettings(contents: Iterable[String]): Unit = {
    // we ignore this, don't know any better solution atm.
    //emittedSettingsString.addAll(contents)
  }

  //  private val quantificationLogger = bookkeeper.logfiles("quantification-problems")

  def assume(term: Term): Unit = {
    if (preamblePhaseOver)
      prover.add(termConverter.convert(term).asInstanceOf[BoolExpr])
    else
      preambleAssumes.add(termConverter.convert(term).asInstanceOf[BoolExpr])
  }





  def assert(goal: Term, timeout: Option[Int]): Boolean = {
    endPreamblePhase()
    setTimeout(timeout)

    val (result, duration) = Verifier.config.assertionMode() match {
      case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal)
      case Config.AssertionMode.PushPop => assertUsingPushPop(goal)
    }
    result
  }

  protected def assertUsingPushPop(goal: Term): (Boolean, Long) = {
    endPreamblePhase()
    push()

    val negatedGoal = ctx.mkNot(termConverter.convert(goal).asInstanceOf[BoolExpr])
    prover.add(negatedGoal)
    val startTime = System.currentTimeMillis()
    val res = prover.check()
    ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB_FULL)
    val endTime = System.currentTimeMillis()
    pop()

    //    if (!result) {
    //      retrieveAndSaveModel()
    //    }

    (res == Status.UNSATISFIABLE, endTime - startTime)
  }

  def saturate(data: Option[Config.ProverStateSaturationTimeout]): Unit = {
    endPreamblePhase()
    data match {
      case Some(Config.ProverStateSaturationTimeout(timeout, comment)) => saturate(timeout, comment)
      case None => /* Don't do anything */
    }
  }

  def saturate(timeout: Int, comment: String): Unit = {
    endPreamblePhase()
//    this.comment(s"State saturation: $comment")
    setTimeout(Some(timeout))
    prover.check()
  }

  protected def retrieveAndSaveModel(): Unit = {
//    if (Verifier.config.counterexample.toOption.isDefined) {
//      writeLine("(get-model)")
//
//      var model = readModel("\n").trim()
//      if (model.startsWith("\"")) {
//        model = model.replaceAll("\"", "")
//      }
//      lastModel = model
//    }
    null
  }

  protected def assertUsingSoftConstraints(goal: Term): (Boolean, Long) = {
    endPreamblePhase()
//    val guard = fresh("grd", Nil, sorts.Bool)
//
//    writeLine(s"(assert (=> $guard (not $goal)))")
//    readSuccess()
//
//    val startTime = System.currentTimeMillis()
//    writeLine(s"(check-sat $guard)")
//    val result = readUnsat()
//    val endTime = System.currentTimeMillis()
//
//    if (!result) {
//      retrieveAndSaveModel()
//    }
//
//    (result, endTime - startTime)
    ???
  }

  def check(timeout: Option[Int] = None): Result = {
    endPreamblePhase()
    setTimeout(timeout)

    val res = prover.check()

    res match {
      case Status.SATISFIABLE => Sat
      case Status.UNSATISFIABLE => Unsat
      case Status.UNKNOWN=> Unknown
    }
  }

  def endPreamblePhase() =  {


    if (!preamblePhaseOver) {
      preamblePhaseOver = true

      val merged = emittedPreambleString.mkString("\n")
      val parsed = ctx.parseSMTLIB2String(merged, emittedSortSymbols.toArray, emittedSorts.toArray, emittedFuncSymbols.toArray, emittedFuncs.toArray)
      prover.add(parsed: _*)
      prover.add(preambleAssumes.toSeq : _*)
      preambleAssumes.clear()
    }
  }

  def statistics(): Map[String, String] = {
//    var repeat = true
//    var line = ""
//    var stats = scala.collection.immutable.SortedMap[String, String]()
//    val entryPattern = """\(?\s*:([A-za-z\-]+)\s+((?:\d+\.)?\d+)\)?""".r
//
//    writeLine("(get-info :all-statistics)")
//
//    do {
//      line = readLineFromInput()
//      comment(line)
//
//      /* Check that the first line starts with "(:". */
//      if (line.isEmpty && !line.startsWith("(:"))
//        throw ProverInteractionFailed(uniqueId, s"Unexpected output of prover while reading statistics: $line")
//
//      line match {
//        case entryPattern(entryName, entryNumber) =>
//          stats = stats + (entryName -> entryNumber)
//        case _ =>
//      }
//
//      repeat = !line.endsWith(")")
//    } while (repeat)
//
//    toMap(stats)
    Map.empty
  }

  def comment(str: String): Unit = {
    if (!preamblePhaseOver && str == "End preamble")
      endPreamblePhase()
  }

  def fresh(name: String, argSorts: Seq[Sort], resultSort: Sort): Fun = {
    val id = identifierFactory.fresh(name)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)

    termConverter.convert(decl)

    fun
  }

  def declare(decl: Decl): Unit = {
    // just creating the term is enough.
    decl match {
      case SortDecl(s) => {
        val convertedSort = termConverter.convertSort(s)
        val convertedSortSymbol = termConverter.convertSortSymbol(s)
        if (convertedSortSymbol.isDefined) {
          emittedSortSymbols.add(convertedSortSymbol.get)
          emittedSorts.add(convertedSort)
        }
      }
      case fd@FunctionDecl(f) => {
        val converted = termConverter.convert(fd)
        if (!emittedFuncs.contains(converted)){
          emittedFuncs.add(converted)
          emittedFuncSymbols.append(termConverter.convertFuncSymbol(fd))
        }
      }
      case MacroDecl(id, args, body) if expandMacros => termConverter.macros.update(id.name, (args, body))
      case md: MacroDecl if !expandMacros => {
        val (convertedFunc, axiom) = termConverter.convert(md)
        if (!emittedFuncs.contains(convertedFunc)){
          emittedFuncs.add(convertedFunc)
          emittedFuncSymbols.append(convertedFunc.getName)
        }
        if (preamblePhaseOver){
          prover.add(axiom)
        }else{
          preambleAssumes.add(axiom)
        }
      }
      case swd@SortWrapperDecl(from, to) => {
        val converted = termConverter.convert(swd)
        if (!emittedFuncs.contains(converted)){
          emittedFuncs.add(converted)
          emittedFuncSymbols.append(termConverter.convertSortWrapperSymbol(swd))
        }
      }
    }
  }





  protected def readModel(separator: String): String = {
//    try {
//      var endFound = false
//      val result = new mutable.StringBuilder
//      var firstTime = true
//      while (!endFound) {
//        val nextLine = readLineFromInput()
//        if (nextLine.trim().endsWith("\"") || (firstTime && !nextLine.startsWith("\""))) {
//          endFound = true
//        }
//        result.append(separator).append(nextLine)
//        firstTime = false
//      }
//      result.result()
//    } catch {
//      case e: Exception =>
//        println("Error reading model: " + e)
//        ""
//    }
    null
  }



  protected def logToFile(str: String): Unit = {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }


  override def getLastModel(): String = lastModel

  override def clearLastModel(): Unit = lastModel = null

  protected def setTimeout(timeout: Option[Int]): Unit = {
    val effectiveTimeout = timeout.getOrElse(Verifier.config.proverTimeout)

    /* [2015-07-27 Malte] Setting the timeout unnecessarily often seems to
     * worsen performance, if only a bit. For the current test suite of
     * 199 Silver files, the total verification time increased from 60s
     * to 70s if 'set-option' is emitted every time.
     */
    if (lastTimeout != effectiveTimeout) {
      lastTimeout = effectiveTimeout

      if(Verifier.config.proverEnableResourceBounds) {
        ctx.updateParamValue("rlimit", (effectiveTimeout * Verifier.config.proverResourcesPerMillisecond).toString)
      } else {
        ctx.updateParamValue("timeout", effectiveTimeout.toString)
      }
    }
  }

  override def name: String = Z3ProverAPI.name

  override def minVersion: Version = Z3ProverAPI.minVersion

  override def maxVersion: Option[Version] = Z3ProverAPI.maxVersion

  override def staticPreamble: String = Z3ProverAPI.staticPreamble

  override def randomizeSeedsOptions: Seq[String] = Z3ProverAPI.randomizeSeedsOptions
}
