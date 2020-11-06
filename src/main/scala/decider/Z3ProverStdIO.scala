// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import java.io.{PrintWriter, StringReader}

import scala.collection.JavaConverters._
import scala.collection.mutable
import com.microsoft.z3
import com.typesafe.scalalogging.LazyLogging
import org.scalactic.TimesOnInt.convertIntToRepeater
import smtlib.trees.Commands._
import smtlib.trees.Terms.SSymbol
import viper.silicon.{Config, Map}
import viper.silicon.common.config.Version
import viper.silicon.interfaces.decider.{Prover, Sat, Unknown, Unsat}
import viper.silicon.reporting.Z3InteractionFailed
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.plugin.PluginAwareReporter

class Z3ProverStdIO(uniqueId: String,
                    termConverter: TermToSMTLib2Converter,
                    identifierFactory: IdentifierFactory,
                    reporter: PluginAwareReporter)
    extends Prover
       with LazyLogging {

  private var pushPopScopeDepth = 0
  private var lastTimeout: Int = -1
  private var logfileWriter: PrintWriter = _
  private var ctx: z3.Context = _
  private var solver: z3.Solver = _
  var lastModel : String = null
  var sortMap: mutable.Map[String, z3.Sort] = _
  var sortSymbols: Array[z3.Symbol] = _
  var sortTypes: Array[z3.Sort] = _
  var funMap: mutable.Map[String, z3.FuncDecl] = _
  var funSymbols: Array[z3.Symbol] = _
  var funDecls: Array[z3.FuncDecl] = _

  /// Not very robust, but they work for Silicon.
  private object Patterns {
    val Assert = """\(assert (.*)\)""".r
    val SetOption = """\(set-option :([-_A-Za-z0-9$.]+) ("?[^"]+"?)\)[^(]*""".r
    val DeclareSort = """\(declare-sort ([A-Za-z$.]+)\s?(\d+)?\)""".r
    val DefineSort = """\(define-sort ([A-Za-z$.]+) \(\) ([A-Za-z]+)\)""".r
    val DeclareConst = """\(declare-const ([A-Za-z$._]+) ([A-Za-z$.<>_]+)\)""".r
    val DefineConst = """\(define-const ([A-Za-z$.]+) ([A-Za-z$.]+) ([A-Za-z0-9$.]+)\)""".r
    val Int = """\d+""".r
    val Double = """\|\d+\.\d+\|""".r
  }

  def z3Path(): String = {
    "(dynamic library)"
  }

  def z3Version(): Version = {
    val versionPattern = """\(?\s*:version\s+"(.*?)(?:\s*-.*?)?"\)?""".r
    val line = ":version \"" + z3.Version.getFullVersion().stripPrefix("Z3 ") + "\""
    comment(line)

    line match {
      case versionPattern(v) => Version(v)
      case _ => throw Z3InteractionFailed(uniqueId, s"Unexpected output of Z3 while getting version: $line")
    }
  }

  def start() {
    pushPopScopeDepth = 0
    lastTimeout = -1
    logfileWriter = if (Verifier.config.disableTempDirectory()) null else viper.silver.utility.Common.PrintWriter(Verifier.config.z3LogFile(uniqueId).toFile)
    z3.Global.ToggleWarningMessages(true)

    // Initialize Z3 via the API
    val cfg = Map[String, String](
      //"global-decls" -> "true"
    )
    ctx = new z3.Context(mapAsJavaMap(cfg))
    solver = ctx.mkSolver()
    sortMap = mutable.Map(
      "Int" -> ctx.getIntSort,
      "Bool" -> ctx.getBoolSort,
      "Real" -> ctx.getRealSort,
    )
    sortSymbols = Array()
    sortTypes = Array()
    funMap = mutable.Map()
    funSymbols = Array()
    funDecls = Array()
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

      if (logfileWriter != null) {
        logfileWriter.close()
      }
    }

    solver = null
    ctx = null
    sortMap = null
    sortSymbols = null
    sortTypes = null
    funMap = null
    funSymbols = null
    funDecls = null
  }

  def push(n: Int = 1) {
    pushPopScopeDepth += n
    val cmd = (if (n == 1) "(push)" else "(push " + n + ")") + " ; " + pushPopScopeDepth
    logToFile(cmd)
    n times { solver.push() }
  }

  def pop(n: Int = 1) {
    val cmd = (if (n == 1) "(pop)" else "(pop " + n + ")") + " ; " + pushPopScopeDepth
    pushPopScopeDepth -= n
    logToFile(cmd)
    solver.pop(n)
  }

  private def registerSort(name: String, mkSort: (z3.Symbol) => z3.Sort): z3.Sort = {
    val symbol = ctx.mkSymbol(name)
    val sort = mkSort(symbol)
    sortMap.update(name, sort)
    // FIXME: this is inefficient as it makes a copy of the array each time.
    sortSymbols = sortSymbols :+ symbol
    sortTypes = sortTypes :+ sort
    sort
  }

  private def registerFuncDecl(name: String, mkSort: (z3.Symbol) => z3.FuncDecl): z3.FuncDecl = {
    val symbol = ctx.mkSymbol(name)
    val funDecl = mkSort(symbol)
    funMap.update(name, funDecl)
    // FIXME: this is inefficient as it makes a copy of the array each time.
    funSymbols = funSymbols :+ symbol
    funDecls = funDecls :+ funDecl
    funDecl
  }

  private def parseCommand(cmd: String): Command = {
    val input = new StringReader(cmd)
    val lexer = new smtlib.lexer.Lexer(input)
    val parser = new smtlib.parser.Parser(lexer)
    parser.parseCommand
  }

  def emit(content: String) {
    logToFile(content)

    // HACK: There are too many uses of `emit()`, so we are forced to interpret the command.
    val command = content.replace("\t", " ").replace("\n", " ")
    command match {
      case Patterns.Assert(_) =>
        parseSMTLIB2Command(command).foreach(solver.add(_))
      // FIXME: It seems that these options are not allowed. Why?
      case Patterns.SetOption(key, value) if
          key == "global-decls" || key == "print-success" || key == "type_check" || key == "smt.qi.cost"
            || key.startsWith("fp.spacer") || key == "smt.random_seed" || key.startsWith("sls.") => // Skip
      case Patterns.SetOption(key, value) =>
        val p = ctx.mkParams()
        value match {
          case "true" => p.add(key, true)
          case "false" => p.add(key, false)
          case Patterns.Int() if key == "smt.qi.eager_threshold" => p.add(key, value.toDouble)
          case Patterns.Int() => p.add(key, value.toInt)
          case Patterns.Double() => p.add(key, value.stripPrefix("|").stripSuffix("|").toDouble)
          case _ => p.add(key, value)
        }
        solver.setParameters(p)
      case Patterns.DeclareSort(name, arity) if arity == null || arity == "0" =>
        registerSort(name, ctx.mkUninterpretedSort(_))
      case Patterns.DefineSort(name, ref) if ref == "Real" =>
        registerSort(name, _ => ctx.mkRealSort())
      case Patterns.DeclareConst(name, sortName) =>
        registerFuncDecl(name, ctx.mkFuncDecl(_, Array[z3.Sort](), sortMap(sortName)))
      case Patterns.DefineConst(name, sortName, body) =>
        registerFuncDecl(name, ctx.mkFuncDecl(_, Array[z3.Sort](), sortMap(sortName)))
        parseSMTLIB2Command(s"(assert (= $name $body))").foreach(solver.add(_))
      case complex_command =>
        parseCommand(complex_command) match {
          case DeclareFun(SSymbol(name), params, returnSort) =>
            val paramSorts = params.map(_.toString).map(sortMap).toArray
            registerFuncDecl(name, ctx.mkFuncDecl(_, paramSorts, sortMap(returnSort.toString)))
          case DefineFun(FunDef(SSymbol(name), params, returnSort, body)) =>
            val paramSorts = params.map(_.sort.toString).map(sortMap).toArray
            registerFuncDecl(name, ctx.mkFuncDecl(_, paramSorts, sortMap(returnSort.toString)))
            val paramNames = params.map(_.name.name)
            val vars = params.map(p => s"(${p.name.name} ${p.sort.toString})")
            val triggers = s":pattern (($name ${paramNames.mkString(" ")}))"
            parseSMTLIB2Command(
              s"(assert (forall (${vars.mkString(" ")}) (! (= ($name ${paramNames.mkString(" ")}) $body) $triggers)))"
            ).foreach(solver.add(_))
          case DeclareDatatypes(Seq((SSymbol(name), constructors))) =>
            val localSortMap = (sortName: String) => if (sortName == name) { null } else { sortMap(name) }
            var z3Constructors = Seq[z3.Constructor]()
            for (constructor <- constructors) {
              z3Constructors = z3Constructors :+ ctx.mkConstructor(
                constructor.sym.name,
                "is_" + constructor.sym.name, // FIXME: Is this correct? What should we use?
                constructor.fields.map(_._1.name).toArray,
                constructor.fields.map(_._2.toString).map(localSortMap).toArray,
                null
              )
            }
            registerSort(name, ctx.mkDatatypeSort(_, z3Constructors.toArray))
          case todo =>
            // This should be unreachable
            throw new Exception(s"Unhandled SMTLIB2 command: '$todo''")
        }
    }
  }

//  private val quantificationLogger = bookkeeper.logfiles("quantification-problems")

  /// Interpret a smtlib2 command, returning the parsed expressions (e.g. those used in `(assert ...)` commands).
  private def parseSMTLIB2Command(command: String): Array[z3.BoolExpr] = {
    ctx.parseSMTLIB2String(
      command.replace("\n", " ").replace("\t", " "),
      sortSymbols,
      sortTypes,
      funSymbols,
      funDecls
    )
  }

  def assume(term: Term) = {
//    /* Detect certain simple problems with quantifiers.
//     * Note that the current checks don't take in account whether or not a
//     * quantification occurs in positive or negative position.
//     */
//    term.deepCollect{case q: Quantification => q}.foreach(q => {
//      val problems = QuantifierSupporter.detectQuantificationProblems(q)
//
//      if (problems.nonEmpty) {
//        quantificationLogger.println(solver"\n\n${q.toString(true)}")
//        quantificationLogger.println("Problems:")
//        problems.foreach(p => quantificationLogger.println(s"  $p"))
//      }
//    })

    assume(termConverter.convert(term))
  }

  def assume(term: String) {
//    bookkeeper.assumptionCounter += 1

    logToFile("(assert " + term + ")")
    parseSMTLIB2Command("(assert " + term + ")").foreach(solver.add(_))
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

    comment(s"${viper.silver.reporter.format.formatMillisReadably(duration)}")
    comment("(get-info :all-statistics)")

    result
  }

  private def assertUsingPushPop(goal: String): (Boolean, Long) = {
    push()

    logToFile("(assert (not " + goal + "))")
    parseSMTLIB2Command("(assert (not " + goal + "))").foreach(solver.add(_))

    val startTime = System.currentTimeMillis()
    val result = solver.check() == z3.Status.UNSATISFIABLE
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
    logToFile("(check-sat)")
    solver.check()
  }

  private def getModel(): Unit = {
    if (Verifier.config.counterexample.toOption.isDefined) {
      logToFile("(get-model)")
      lastModel = solver.getModel.toString
    }
  }

  private def assertUsingSoftConstraints(goal: String): (Boolean, Long) = {
    val guard = fresh("grd", Nil, sorts.Bool)

    logToFile(s"(assert (implies $guard (not $goal)))")
    parseSMTLIB2Command(s"(assert (implies $guard (not $goal)))").foreach(solver.add(_))

    val startTime = System.currentTimeMillis()
    logToFile(s"(check-sat $guard)")
    val result = solver.check() == z3.Status.UNSATISFIABLE
    val endTime = System.currentTimeMillis()

    if (!result) {
      getModel()
    }

    (result, endTime - startTime)
  }

  def check(timeout: Option[Int] = None) = {
    setTimeout(timeout)

    logToFile("(check-sat)")

    solver.check() match {
      case z3.Status.SATISFIABLE => Sat
      case z3.Status.UNSATISFIABLE => Unsat
      case z3.Status.UNKNOWN => Unknown
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

      if(Verifier.config.z3EnableResourceBounds()) {
        logToFile(s"(set-option :rlimit ${effectiveTimeout * (Verifier.config.z3ResourcesPerMillisecond())})")
        val p = ctx.mkParams()
        p.add("rlimit", effectiveTimeout * (Verifier.config.z3ResourcesPerMillisecond()))
        solver.setParameters(p)
      } else {
        logToFile(s"(set-option :timeout $effectiveTimeout)")
        val p = ctx.mkParams()
        p.add("timeout", effectiveTimeout)
        solver.setParameters(p)
      }
    }
  }

  def statistics(): Map[String, String]= {
    // TODO
    Map()
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

    declare(decl)

    fun
  }

  def declare(decl: Decl) {
    val str = termConverter.convert(decl)
    logToFile(str)

    decl match {
      case SortDecl(sort: Sort) =>
        val name: String = termConverter.convert(sort)
        registerSort(name, ctx.mkUninterpretedSort(_))

      case FunctionDecl(fun: Function) =>
        val idDoc: String = termConverter.render(fun.id)
        val z3ArgSortsDoc = fun.argSorts.map(termConverter.convert).filter(_ != "").map(sortMap).toArray
        val z3ResultSortDoc = sortMap(termConverter.convert(fun.resultSort))
        registerFuncDecl(idDoc, ctx.mkFuncDecl(_, z3ArgSortsDoc, z3ResultSortDoc))

      case swd @ SortWrapperDecl(from, to) =>
        val idDoc: String = termConverter.render(swd.id)
        val z3ArgSortDoc = sortMap(termConverter.convert(from))
        val z3ResultSortDoc = sortMap(termConverter.convert(to))
        registerFuncDecl(idDoc, ctx.mkFuncDecl(_, z3ArgSortDoc, z3ResultSortDoc))

      case MacroDecl(id, args, body) =>
        val idDoc: String = termConverter.render(id)
        val z3ArgSortsDoc = args.map(_.sort).map(termConverter.convert).map(sortMap).toArray
        val z3ResultSortDoc = sortMap(termConverter.convert(body.sort))
        registerFuncDecl(idDoc, ctx.mkFuncDecl(_, z3ArgSortsDoc, z3ResultSortDoc))

        // HACK: Convert a Term to a Z3 expression by generating and parsing a SMTLIB2 command.
        val paramNames = args.map(_.id.name)
        val vars = args.map(p => s"(${p.id.name} ${termConverter.convert(p.sort)})")
        val triggers = s":pattern (($idDoc ${paramNames.mkString(" ")}))"
        parseSMTLIB2Command(
          s"(assert (forall (${vars.mkString(" ")}) (! (= ($idDoc ${paramNames.mkString(" ")}) ${termConverter.convert(body)}) $triggers)))"
        ).foreach(solver.add(_))
    }
  }

//  def resetAssertionCounter() { bookkeeper.assertionCounter = 0 }
//  def resetAssumptionCounter() { bookkeeper.assumptionCounter = 0 }

//  def resetCounters() {
//    resetAssertionCounter()
//    resetAssumptionCounter()
//  }

  private def logToFile(str: String) {
    if (logfileWriter != null) {
      logfileWriter.println(str)
    }
  }

  override def getLastModel(): String = lastModel

  override def clearLastModel(): Unit = lastModel = null
}
