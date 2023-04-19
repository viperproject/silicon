// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.decider

import com.typesafe.scalalogging.LazyLogging
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Result, Sat, Unknown, Unsat}
import viper.silicon.state.{IdentifierFactory, State}
import viper.silicon.state.terms.{App, Decl, Fun, FunctionDecl, Implies, Ite, MacroDecl, Quantification, Sort, SortDecl, SortWrapperDecl, Term, Trigger, TriggerGenerator, sorts}
import viper.silicon.{Config, Map}
import viper.silicon.verifier.Verifier
import viper.silver.reporter.{InternalWarningMessage, Reporter}
import viper.silver.verifier.{MapEntry, ModelEntry, ModelParser, ValueEntry, DefaultDependency => SilDefaultDependency, Model => ViperModel}

import java.io.PrintWriter
import java.nio.file.Path
import scala.collection.mutable
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_param_kind
import viper.silicon.decider.Z3ProverAPI.oldVersionOnlyParams
import viper.silicon.reporting.ExternalToolError

import scala.jdk.CollectionConverters.MapHasAsJava
import scala.util.Random


object Z3ProverAPI {
  val name = "Z3-API"
  val minVersion = Version("4.8.7.0")
  val maxVersion = Some(Version("4.12.1.0")) /* X.Y.Z if that is the *last supported* version */

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
    "smt.mbqi" -> false,
    //"pp.bv_literals" -> false,  // This is part of z3config.smt2 but Z3 won't accept it via API.
    "model.v2" -> true
  )
  val intParams = Map(
    "smt.case_split" -> 3,
    "smt.qi.max_multi_patterns" -> 1000,
    "smt.arith.solver" -> 2,
  )
  val stringParams: Map[String, String] = Map(
    // currently none
  )
  val doubleParams = Map(
    "smt.qi.eager_threshold" -> 100.0,
  )
  val allParams = boolParams ++ intParams ++ stringParams ++ doubleParams
  val oldVersionOnlyParams = Set("smt.arith.solver")
}


class Z3ProverAPI(uniqueId: String,
                  termConverter: TermToZ3APIConverter,
                  identifierFactory: IdentifierFactory,
                  reporter: Reporter,
                  triggerGenerator: TriggerGenerator)
    extends Prover
      with LazyLogging
{

  /* protected */ var pushPopScopeDepth = 0
  protected var lastTimeout: Int = -1
  protected var prover: Solver = _
  protected var ctx: Context = _

  var proverPath: Path = _
  var lastReasonUnknown : String = _
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
    ctx = new Context(Z3ProverAPI.initialOptions.asJava)
    val params = ctx.mkParams()

    // When setting parameters via API, we have to remove the smt. prefix
    def removeSmtPrefix(s: String) = {
      if (s.startsWith("smt."))
        s.substring(4)
      else
        s
    }

    val useOldVersionParams = version() <= Version("4.8.7.0")
    Z3ProverAPI.boolParams.foreach{
      case (k, v) =>
        if (useOldVersionParams || !oldVersionOnlyParams.contains(k))
          params.add(removeSmtPrefix(k), v)
    }
    Z3ProverAPI.intParams.foreach{
      case (k, v) =>
        if (useOldVersionParams || !oldVersionOnlyParams.contains(k))
          params.add(removeSmtPrefix(k), v)
    }
    Z3ProverAPI.doubleParams.foreach{
      case (k, v) =>
        if (useOldVersionParams || !oldVersionOnlyParams.contains(k))
          params.add(removeSmtPrefix(k), v)
    }
    Z3ProverAPI.stringParams.foreach{
      case (k, v) =>
        if (useOldVersionParams || !oldVersionOnlyParams.contains(k))
          params.add(removeSmtPrefix(k), v)
    }
    val userProvidedArgs = Verifier.config.proverConfigArgs
    prover = ctx.mkSolver()
    val descrs = prover.getParameterDescriptions
    for ((origKey, vl) <- userProvidedArgs) {
      val key = if (origKey.startsWith("smt."))
        origKey.substring(4)
      else
        origKey
      val keySymbol = ctx.mkSymbol(key)
      val param_kind = descrs.getKind(keySymbol)
      param_kind match {
        case Z3_param_kind.Z3_PK_BOOL =>
          params.add(key, vl.toBoolean)
        case Z3_param_kind.Z3_PK_UINT =>
          params.add(key, vl.toInt)
        case Z3_param_kind.Z3_PK_DOUBLE =>
          params.add(key, vl.toDouble)
        case Z3_param_kind.Z3_PK_STRING =>
          params.add(key, vl)
        case _ =>
          reporter.report(InternalWarningMessage("Z3 error: unknown parameter" + key))
      }
    }
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
      case e: Z3Exception =>
        // The only reason we get an exception here is that we've tried to assume a quantifier with an invalid trigger.
        // When used via API, Z3 completely discards assumptions that contain invalid triggers (whereas it just ignores
        // the invalid trigger when used via stdio). Thus, to make sure our assumption is not discarded, we manually
        // walk through all quantifiers and remove invalid terms inside the trigger.
        triggerGenerator.setCustomIsForbiddenInTrigger(triggerGenerator.advancedIsForbiddenInTrigger)
        val cleanTerm = term.transform{
          case q@Quantification(_, _, _, triggers, _, _, _) if triggers.nonEmpty =>
            val goodTriggers = triggers.filterNot(trig => trig.p.exists(ptrn => ptrn.shallowCollect{
              case t => triggerGenerator.isForbiddenInTrigger(t)
            }.nonEmpty))
            q.copy(triggers = goodTriggers)
        }()
        prover.add(termConverter.convert(cleanTerm).asInstanceOf[BoolExpr])
        reporter.report(InternalWarningMessage("Z3 error: " + e.getMessage))
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
      retrieveReasonUnknown()
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

  protected def retrieveReasonUnknown(): Unit = {
    if (Verifier.config.reportReasonUnknown()) {
      lastReasonUnknown = prover.getReasonUnknown
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

      // Setting all options again , since otherwise some of them seem to get lost.
      val standardOptionPrefix = Seq("(set-option :auto_config false)", "(set-option :type_check true)") ++
        Z3ProverAPI.allParams.map(bp => s"(set-option :${bp._1} ${bp._2})")

      val customOptionPrefix = Verifier.config.proverConfigArgs.map(a => s"(set-option :${a._1} ${a._2})")

      val merged = (standardOptionPrefix ++ customOptionPrefix ++ emittedPreambleString).mkString("\n")
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

  override def getReasonUnknown(): String = lastReasonUnknown

  override def clearLastAssert(): Unit = {
    lastReasonUnknown = null
    lastModel = null
  }

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
