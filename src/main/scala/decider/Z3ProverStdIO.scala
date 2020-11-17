// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.decider

import java.io.{PrintWriter, StringReader}

import scala.collection.JavaConverters._
import com.microsoft.z3
import com.typesafe.scalalogging.LazyLogging
import decider.TermToZ3Converter
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
  private var termToZ3Converter: TermToZ3Converter = _
  var lastModel : String = null

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
    termToZ3Converter = new TermToZ3Converter(
      ctx,
      termConverter.convert,
      termConverter.render(_),
      termConverter.convert
    )
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
    termToZ3Converter = null
    if (ctx != null) {
      ctx.close()
    }
    ctx = null
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

  private def parseCommand(cmd: String): Command = {
    val input = new StringReader(cmd)
    val lexer = new smtlib.lexer.Lexer(input)
    val parser = new smtlib.parser.Parser(lexer)
    parser.parseCommand
  }

  def emit(content: String) {
    logToFile(content)

    val command = content.replace("\t", " ").replace("\n", " ")
    command match {
      case Patterns.Assert(_) =>
        val expr = termToZ3Converter.parseCommand(command)
        solver.add(expr)
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
        termToZ3Converter.registerSort(name, ctx.mkUninterpretedSort(_))
      case Patterns.DefineSort(name, ref) if ref == "Real" =>
        termToZ3Converter.registerSort(name, _ => ctx.mkRealSort())
      case Patterns.DeclareConst(name, sortName) =>
        termToZ3Converter.registerFuncDecl(
          name,
          ctx.mkFuncDecl(_, Array[z3.Sort](), termToZ3Converter.getSort(sortName))
        )
      case Patterns.DefineConst(name, sortName, body) =>
        termToZ3Converter.registerFuncDecl(
          name,
          ctx.mkFuncDecl(_, Array[z3.Sort](), termToZ3Converter.getSort(sortName))
        )
        val expr = termToZ3Converter.parseCommand(s"(assert (= $name $body))")
        solver.add(expr)
      case complex_command =>
        parseCommand(complex_command) match {
          case DeclareFun(SSymbol(name), params, returnSort) =>
            val paramSorts = params.map(_.toString).map(termToZ3Converter.getSort).toArray
            termToZ3Converter.registerFuncDecl(
              name,
              ctx.mkFuncDecl(_, paramSorts, termToZ3Converter.getSort(returnSort.toString))
            )
          case DefineFun(FunDef(SSymbol(name), params, returnSort, body)) =>
            val paramSorts = params.map(_.sort.toString).map(termToZ3Converter.getSort).toArray
            termToZ3Converter.registerFuncDecl(
              name,
              ctx.mkFuncDecl(_, paramSorts, termToZ3Converter.getSort(returnSort.toString))
            )
            val paramNames = params.map(_.name.name)
            val vars = params.map(p => s"(${p.name.name} ${p.sort.toString})")
            val triggers = s":pattern (($name ${paramNames.mkString(" ")}))"
            val expr = termToZ3Converter.parseCommand(
              s"(assert (forall (${vars.mkString(" ")}) (! (= ($name ${paramNames.mkString(" ")}) $body) $triggers)))"
            )
            solver.add(expr)
          case DeclareDatatypes(Seq((SSymbol(datatypeSortName), constructors))) =>
            val localSortMap = (sortName: String) => {
              if (sortName == datatypeSortName) {
                null
              } else {
                termToZ3Converter.getSort(sortName)
              }
            }
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
            // Register datatype
            termToZ3Converter.registerSort(datatypeSortName, ctx.mkDatatypeSort(_, z3Constructors.toArray))
            // It seems that there is no need to register the constructor and field accessors
          case todo =>
            // This should be unreachable
            throw new Exception(s"Unhandled SMTLIB2 command: '$todo''")
        }
    }
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
//        quantificationLogger.println(solver"\n\n${q.toString(true)}")
//        quantificationLogger.println("Problems:")
//        problems.foreach(p => quantificationLogger.println(s"  $p"))
//      }
//    })

//    bookkeeper.assumptionCounter += 1

    val command = s"(assert ${termConverter.convert(term)})"
    logToFile(command)
    val expr = termToZ3Converter.parseCommand(command)
    solver.add(expr)
  }

  def assert(goal: Term, timeout: Option[Int] = None) = {
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

  private def assertUsingPushPop(goal: Term): (Boolean, Long) = {
    push()

    val command = "(assert (not " + termConverter.convert(goal) + "))"
    logToFile(command)
    val expr = termToZ3Converter.parseCommand(command)
    solver.add(expr)

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

  private def assertUsingSoftConstraints(goal: Term): (Boolean, Long) = {
    val guard = fresh("grd", Nil, sorts.Bool)

    val command = s"(assert (implies $guard (not ${termConverter.convert(goal)})))"
    logToFile(command)
    val expr = termToZ3Converter.parseCommand(command)
    solver.add(expr)

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
    val command = termConverter.convert(decl)
    logToFile(command)

    termToZ3Converter.declare(decl).foreach(solver.add(_))
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
