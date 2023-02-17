// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Result, Sat, Unknown, Unsat}
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms.{App, Decl, Fun, FunctionDecl, Implies, MacroDecl, Sort, SortDecl, SortWrapperDecl, Term, sorts}
import viper.silicon.{Config, Map}
import viper.silicon.verifier.Verifier
import viper.silver.reporter.{InternalWarningMessage, Reporter}
import viper.silver.verifier.{MapEntry, ModelEntry, ModelParser, ValueEntry, DefaultDependency => SilDefaultDependency, Model => ViperModel}
import java.io.PrintWriter
import java.nio.file.Path

import scala.collection.mutable
import com.microsoft.z3._
import viper.silicon.reporting.ExternalToolError

import scala.jdk.CollectionConverters.MapHasAsJava
import scala.util.Random


object Z3ProverAPI {
  val name = "Z3-API"
  val minVersion = Version("4.8.6.0")
  val maxVersion = Some(Version("4.8.7.0")) /* X.Y.Z if that is the *last supported* version */

  // these are not actually used, but since there is a lot of code that expects command line parameters and a
  // config file, we just supply this information here (whose contents will then be ignored)
  val exeEnvironmentalVariable = "Z3_EXE"
  val dependencies = Seq(SilDefaultDependency("Z3", minVersion.version, "https://github.com/Z3Prover/z3"))
  val staticPreamble = "/z3config.smt2"
  val startUpArgs = Seq("-smt2", "-in")

  val randomizeSeedsSetting = "RANDOMIZE_SEEDS"

  // All options taken from z3config.smt2 and split up according to argument type and time when it has to be set.
  // I removed all options that (no longer?) exist, since those result in errors from Z3.
  val randomizeSeedsOptions = Seq("random_seed")
  val initialOptions = Map("auto_config" -> "false", "type_check" -> "true")
  val boolParams = Map(
    "smt.delay_units" -> true,
    "delay_units" -> true,
    "nnf.sk_hack" -> true,
    "smt.mbqi" -> false,
    "mbqi" -> false,
    "nlsat.randomize" -> true,
    "nlsat.shuffle_vars" -> false,
    "smt.arith.random_initial_value" -> true,
    "arith.random_initial_value" -> true,
    "bv.reflect" -> true,
  )
  val intParams = Map(
    "smt.restart_strategy" -> 0,
    "restart_strategy" -> 0,
    "smt.case_split" -> 3,
    "case_split" -> 3,
    "smt.delay_units_threshold" -> 16,
    "delay_units_threshold" -> 16,
    "smt.qi.max_multi_patterns" -> 1000,
    "qi.max_multi_patterns" -> 1000,
    "smt.phase_selection" -> 0,
    "phase_selection" -> 0,
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
    "restart_factor" -> 1.5,
    "smt.qi.eager_threshold" -> 100.0,
    "qi.eager_threshold" -> 100.0,
  )
}


class Z3ProverAPI(uniqueId: String,
                  termConverter: TermToZ3APIConverter,
                  identifierFactory: IdentifierFactory,
                  reporter: Reporter)
    extends Prover
      with LazyLogging
{

  /* protected */ var pushPopScopeDepth = 0
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

  // If true, we do not define macros on the Z3 level, but perform macro expansion ourselves on Silicon Terms.
  // Otherwise, we define a function on the Z3 level and axiomatize it according to the macro definition.
  // In terms of performance, I could not measure any substantial difference.
  val expandMacros = true



  def version(): Version = {
    var versString = com.microsoft.z3.Version.getFullVersion
    if (versString.startsWith("Z3 "))
      versString = versString.substring(3)
    Version(versString)
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
    termConverter.reset()
    stop()
    start()
  }

  def stop(): Unit = {
    emittedPreambleString.clear()
    preamblePhaseOver = false
    emittedFuncs.clear()
    emittedSorts.clear()
    emittedFuncSymbols.clear()
    emittedSortSymbols.clear()
    prover = null
    lastModel = null
    if (ctx != null){
      ctx.close()
      ctx = null
    }
  }

  def push(n: Int = 1, timeout: Option[Int] = None): Unit = {
    endPreamblePhase()
    setTimeout(timeout)
    pushPopScopeDepth += n
    if (n == 1) {
      // the normal case; we handle this without invoking a bunch of higher order functions
      prover.push()
    } else {
      // this might never actually happen
      (0 until n).foreach(_ => prover.push())
    }
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
    // except we check if someone gives us our custom randomization string, in which
    // case we'll directly set the options to randomize.
    val optionSetString = s"(set-option :${Z3ProverAPI.randomizeSeedsSetting}"
    if (contents.exists(s => s.startsWith(optionSetString))) {
      val params = ctx.mkParams()
      Z3ProverAPI.randomizeSeedsOptions.foreach(o => params.add(o, Random.nextInt(10000)))
      prover.setParameters(params)
    }
  }

  def assume(term: Term): Unit = {
    try {
      if (preamblePhaseOver)
        prover.add(termConverter.convert(term).asInstanceOf[BoolExpr])
      else
        preambleAssumes.add(termConverter.convert(term).asInstanceOf[BoolExpr])
    } catch {
      case e: Z3Exception => reporter.report(InternalWarningMessage("Z3 error: " + e.getMessage))
    }
  }

  def assert(goal: Term, timeout: Option[Int]): Boolean = {
    endPreamblePhase()

    try {
      val (result, _) = Verifier.config.assertionMode() match {
        case Config.AssertionMode.SoftConstraints => assertUsingSoftConstraints(goal, timeout)
        case Config.AssertionMode.PushPop => assertUsingPushPop(goal, timeout)
      }
      result
    } catch {
      case e: Z3Exception => throw ExternalToolError("Prover", "Z3 error: " + e.getMessage)
    }
  }

  protected def assertUsingPushPop(goal: Term, timeout: Option[Int]): (Boolean, Long) = {
    endPreamblePhase()
    push()
    setTimeout(timeout)

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

  protected def assertUsingSoftConstraints(goal: Term, timeout: Option[Int]): (Boolean, Long) = {
    endPreamblePhase()
    setTimeout(timeout)

    val guard = fresh("grd", Nil, sorts.Bool)
    val guardApp = App(guard, Nil)
    val goalImplication = Implies(guardApp, goal)

    prover.add(termConverter.convertTerm(goalImplication).asInstanceOf[BoolExpr])

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

  def endPreamblePhase(): Unit =  {
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
    Map.from(result)
  }

  def comment(str: String): Unit = {
    // ignore
  }

  def fresh(name: String, argSorts: Seq[Sort], resultSort: Sort): Fun = {
    val id = identifierFactory.fresh(name)
    val fun = Fun(id, argSorts, resultSort)
    val decl = FunctionDecl(fun)

    termConverter.convert(decl)

    fun
  }

  def declare(decl: Decl): Unit = {
    // We convert the declaration into a Z3-level declaration (which is automatically added to Z3's
    // current state) and record it in out collection(s) of emmitted declarations.
    // Special handling for macro declarations if expandMacros is true; in that case,
    // nothing is declared on the Z3 level, and we simply remember the definition ourselves.
    decl match {
      case SortDecl(s) =>
        val convertedSort = termConverter.convertSort(s)
        val convertedSortSymbol = termConverter.convertSortSymbol(s)
        if (convertedSortSymbol.isDefined) {
          emittedSortSymbols.add(convertedSortSymbol.get)
          emittedSorts.add(convertedSort)
        }
      case fd: FunctionDecl =>
        val converted = termConverter.convert(fd)
        if (!emittedFuncs.contains(converted)){
          emittedFuncs.add(converted)
          emittedFuncSymbols.append(termConverter.convertFuncSymbol(fd))
        }
      case MacroDecl(id, args, body) if expandMacros => termConverter.macros.update(id.name, (args, body))
      case md: MacroDecl =>
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
      case swd: SortWrapperDecl =>
        val converted = termConverter.convert(swd)
        if (!emittedFuncs.contains(converted)){
          emittedFuncs.add(converted)
          emittedFuncSymbols.append(termConverter.convertSortWrapperSymbol(swd))
        }
    }
  }

  protected def logToFile(str: String): Unit = {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }

  override def getModel(): ViperModel = {
    val entries = new mutable.HashMap[String, ModelEntry]()
    for (constDecl <- lastModel.getConstDecls){
      val constInterp = lastModel.getConstInterp(constDecl)
      val constName = constDecl.getName.toString
      val entry = fastparse.parse(constInterp.toString, ModelParser.value(_)).get.value
      entries.update(constName, entry)
    }
    for (funcDecl <- lastModel.getFuncDecls) {
      val funcInterp = lastModel.getFuncInterp(funcDecl)
      val options = new mutable.HashMap[Seq[ValueEntry], ValueEntry]()
      for (entry <- funcInterp.getEntries) {
        val args = entry.getArgs.map(arg => fastparse.parse(arg.toString, ModelParser.value(_)).get.value)
        val value = fastparse.parse(entry.getValue.toString, ModelParser.value(_)).get.value
        options.update(args.toIndexedSeq, value)
      }
      val els = fastparse.parse(funcInterp.getElse.toString, ModelParser.value(_)).get.value
      entries.update(funcDecl.getName.toString, MapEntry(options.toMap, els))
    }
    ViperModel(entries.toMap)
  }

  override def hasModel(): Boolean = {
    lastModel != null
  }

  override def isModelValid(): Boolean = {
    lastModel != null
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

  lazy val name: String = Z3ProverAPI.name

  lazy val minVersion: Version = Z3ProverAPI.minVersion

  lazy val maxVersion: Option[Version] = Z3ProverAPI.maxVersion

  lazy val staticPreamble: String = Z3ProverAPI.staticPreamble

  lazy val randomizeSeedsOptions: Seq[String] = {
    Seq(Z3ProverAPI.randomizeSeedsSetting)
  }
}
