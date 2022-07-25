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
import viper.silicon.state.terms.{App, Decl, Fun, FunctionDecl, Implies, MacroDecl, Sort, SortDecl, SortWrapperDecl, Term, sorts}
import viper.silicon.{Config, Map, toMap}
import viper.silicon.verifier.Verifier
import viper.silver.reporter.{ConfigurationConfirmation, InternalWarningMessage, Reporter}
import viper.silver.verifier.{DefaultDependency => SilDefaultDependency, Model => ViperModel}
import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.nio.file.{Path, Paths}
import java.util.concurrent.TimeUnit

import scala.collection.mutable
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_ast_print_mode

import scala.collection.immutable.ListMap
import scala.jdk.CollectionConverters
import scala.jdk.CollectionConverters.MapHasAsJava


object Z3ProverAPI {
  val name = "Z3-API"
  val minVersion = Version("4.5.0")
  val maxVersion = None // Some(Version("4.5.0")) /* X.Y.Z if that is the *last supported* version */
  val exeEnvironmentalVariable = "Z3_EXE"
  val dependencies = Seq(SilDefaultDependency("Z3", minVersion.version, "https://github.com/Z3Prover/z3"))

  val initialOptions = Map("auto_config" -> "false", "type_check" -> "true")
  val boolParams = Map(
    "smt.delay_units" -> true,
    "nnf.sk_hack" -> true,
    "smt.mbqi" -> false,
    "nlsat.randomize" -> true,
    "nlsat.shuffle_vars" -> false,
    "smt.arith.random_initial_value" -> true,
  )
  val intParams = Map("smt.restart_strategy" -> 0,
    "smt.case_split" -> 3,
    "smt.delay_units_threshold" -> 16,
    "smt.qi.max_multi_patterns" -> 1000,
    "smt.phase_selection" -> 0,
    "sat.random_seed" -> 0,
    "nlsat.seed" -> 0,
    "random_seed" -> 0,
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
  var lastModel : Model = _

  var emittedPreambleString = mutable.Queue[String]()
  var preamblePhaseOver = false
  var preambleAssumes = mutable.LinkedHashSet[BoolExpr]()
  val emittedSorts = mutable.LinkedHashSet[com.microsoft.z3.Sort]()
  val emittedSortSymbols = mutable.LinkedHashSet[Symbol]()
  val emittedFuncs = mutable.LinkedHashSet[FuncDecl]()
  val emittedFuncSymbols = mutable.Queue[Symbol]()





  def version(): Version = {
    val versString = com.microsoft.z3.Version.getFullVersion
    if (!versString.startsWith("Z3 "))
      sys.error("unexpected version string")
    Version(versString.substring(3))
  }

  def start(): Unit = {
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = if (Verifier.config.disableTempDirectory()) null else viper.silver.utility.Common.PrintWriter(Verifier.config.proverLogFile(uniqueId).toFile)
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

  def reset(): Unit = {
    stop()
    termConverter.reset()
    start()
  }

  def stop(): Unit = {
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
    if (n != 1)
      sys.error("Not supported")
    prover.push()
  }

  def pop(n: Int = 1): Unit = {
    endPreamblePhase()
    prover.pop(n)
    pushPopScopeDepth -= n
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
    // our settings are defined in this class (see above).
  }

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
    val endTime = System.currentTimeMillis()
    val result = res == Status.UNSATISFIABLE
    pop()

    if (!result) {
      retrieveAndSaveModel()
    }

    (result, endTime - startTime)
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
    setTimeout(Some(timeout))
    prover.check()
  }

  protected def retrieveAndSaveModel(): Unit = {
    if (Verifier.config.counterexample.toOption.isDefined) {
      val model = prover.getModel
      lastModel = model
    }
  }

  protected def assertUsingSoftConstraints(goal: Term): (Boolean, Long) = {
    endPreamblePhase()
    val guard = fresh("grd", Nil, sorts.Bool)
    val guardApp = App(guard, Nil)
    val goalImplication = Implies(guardApp, goal)

    prover.add(termConverter.convertTerm(goalImplication))

    val startTime = System.currentTimeMillis()
    val res = prover.check(termConverter.convertTerm(guardApp))
    val endTime = System.currentTimeMillis()
    val result = res == Status.UNSATISFIABLE
    if (!result) {
      retrieveAndSaveModel()
    }

    (result, endTime - startTime)
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
    val statistics = prover.getStatistics
    val result = mutable.HashMap[String, String]()
    for (e <- statistics.getEntries()) {
      result.update(e.Key, e.getValueString)
    }
    ListMap.from(result)
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
      case md@MacroDecl(id, args, body) => termConverter.macros.update(id.name, (args, body))
      case swd@SortWrapperDecl(from, to) => {
        val converted = termConverter.convert(swd)
        if (!emittedFuncs.contains(converted)){
          emittedFuncs.add(converted)
          emittedFuncSymbols.append(termConverter.convertSortWrapperSymbol(swd))
        }
      }
    }
  }

  protected def logToFile(str: String): Unit = {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }

  override def getModel(): ViperModel = {
    for (constDecl <- lastModel.getConstDecls){
      val constInterp = lastModel.getConstInterp(constDecl)
    }
    for (funcDecl <- lastModel.getFuncDecls) {
      val funcInterp = lastModel.getFuncInterp(funcDecl)
    }
    null
  }

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
