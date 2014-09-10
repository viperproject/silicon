/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package theories

import com.weiglewilczek.slf4s.Logging
import silver.ast.utility.Functions
import silver.components.StatefulComponent
import silver.verifier.errors.{Internal, FunctionNotWellformed, PostconditionViolated}
import interfaces.{Failure, VerificationResult, Consumer, Producer, Evaluator, Success}
import interfaces.decider.Decider
import interfaces.state.{Chunk, StateFactory, State, PathConditions, Heap, Store, Mergeable}
import interfaces.state.factoryUtils.Ø
import state.{DefaultContext, SymbolConvert, DirectChunk}
import state.terms.{utils => _, _}
import state.terms.predef._

case class SnapshotRecorder(currentSnap: Term = null,
                            locToChunk: Map[ast.LocationAccess, Chunk] = Map(),
                            chunkToSnap: Map[Chunk, Term] = Map(),
                            fappToSnap: Map[ast.FuncApp, Term] = Map())
    extends Mergeable[SnapshotRecorder] {

  def locToSnap = locToChunk.map{case (loc, ch) => loc -> chunkToSnap(ch)}

  def merge(other: SnapshotRecorder): SnapshotRecorder = {
    val combinedCtsOrConflicts = utils.conflictFreeUnion(chunkToSnap, other.chunkToSnap)
    val combinedLtcOrConflicts = utils.conflictFreeUnion(locToChunk, other.locToChunk)
    val combinedFtsOrConflicts = utils.conflictFreeUnion(fappToSnap, other.fappToSnap)

    (combinedCtsOrConflicts, combinedLtcOrConflicts, combinedFtsOrConflicts) match {
      case (Right(cts), Right(ltc), Right(fts)) /*if currentSnap == other.currentSnap*/ =>

        copy(chunkToSnap = cts, locToChunk = ltc, fappToSnap = fts)

      case p3 =>
        p3.productIterator.zip[String](Seq("cts", "ltc", "fts").iterator).foreach{case (a,b) =>
          println(s"$b: $a")
        }

        sys.error("Unexpected situation while merging snapshot recorders")
    }
  }

  override lazy val toString = {
    val ltcStrs = locToChunk map {case (k, v) => s"$k  |==>  $v"}
    val ctsStrs = chunkToSnap map {case (k, v) => s"$k  |==>  $v"}
    val ltsStrs = locToSnap map {case (k, v) => s"$k  |==>  $v"}
    val ftsStrs = fappToSnap map {case (k, v) => s"$k  |==>  $v"}

    s"""SnapshotRecorder(
       |  currentSnap: $currentSnap
       |  locToChunk:
       |    ${ltcStrs.mkString("\n    ")}
       |  chunkToSnap:
       |    ${ctsStrs.mkString("\n    ")}
       |  locToSnap:
       |    ${ltsStrs.mkString("\n    ")}
       |  fappToSnap:
       |    ${ftsStrs.mkString("\n    ")}
       |)
     """.stripMargin
  }
}

trait FunctionsSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext]
            with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext]
            with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type AxiomGenerator = () => Quantification

  val config: Config

  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
  import decider.{fresh, inScope}

  val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  val symbolConverter: SymbolConvert

  private val expressionTranslator =
    new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh, limitedFunction)

  private class FunctionData(val programFunction: ast.ProgramFunction, val program: ast.Program) {
    val func = symbolConverter.toFunction(programFunction)
    val formalArgs = programFunction.formalArgs map (v => Var(v.name, symbolConverter.toSort(v.typ)))
    val args = Seq(`?s`) ++ formalArgs
    val fapp = FApp(func, `?s`, formalArgs)
    val triggers = Trigger(fapp :: Nil) :: Nil

    val limitedFunc = limitedFunction(func)
    val limitedFapp = FApp(limitedFunc, `?s`, formalArgs)
    val limitedTriggers = Trigger(limitedFapp :: Nil) :: Nil

    val limitedAxiom = {
      val limFApp = FApp(limitedFunc, `?s`, formalArgs)

      Quantification(Forall, args, limFApp === fapp, triggers)
    }

    /* If the program function isn't well-formed, the following collections might remain empty */
    var optLocToSnap: Option[Map[ast.LocationAccess, Term]] = None
    var optFappToSnap: Option[Map[ast.FuncApp, Term]] = None

    def locToSnap = optLocToSnap.getOrElse(Map[ast.LocationAccess, Term]())
    def fappToSnap = optFappToSnap.getOrElse(Map[ast.FuncApp, Term]())

    lazy val translatedPre = {
      val pre = ast.utils.BigAnd(programFunction.pres)

      expressionTranslator.translatePrecondition(program, pre, locToSnap, fappToSnap)
    }

    lazy val axiom = {
      val translatedBody = expressionTranslator.translate(program, programFunction, locToSnap, fappToSnap)

      val nonNulls = state.terms.utils.BigAnd(
        programFunction.exp.deepCollect{case fa: ast.FieldAccess => fa.rcv}
                           .map(rcv => expressionTranslator.translate(program, rcv, locToSnap, fappToSnap) !== Null())
                           .toSet[Term])

      Quantification(Forall, args, Implies(translatedPre, And(fapp === translatedBody, nonNulls)), triggers)
    }

    lazy val postAxiom = {
      if (programFunction.posts.nonEmpty) {
        val post = ast.utils.BigAnd(programFunction.posts)

        val translatedPost =
          expressionTranslator.translatePostcondition(program, post, locToSnap, fappToSnap, limitedFapp)

        Quantification(Forall, args, Implies(translatedPre, translatedPost), limitedTriggers)
      } else
        True()
    }
  }

  private def limitedFunction(funcSymbol: Function) =
    Function(funcSymbol.id + "$", funcSymbol.sort)

  object functionsSupporter extends StatefulComponent {
    private var program: ast.Program = null

    private var functionData = Map[ast.ProgramFunction, FunctionData]()

    def handleFunctions(program: ast.Program): List[VerificationResult] =  {
      reset()
      analyze(program)

      decider.prover.logComment("-" * 60)
      decider.prover.logComment("Declaring program functions")
      declareFunctions()

      val c = DefaultContext(program = program, snapshotRecorder = Some(SnapshotRecorder(currentSnap = `?s`)))

      functionData.keys.flatMap(function => handleFunction(function, c)).toList
    }

    private def analyze(program: ast.Program) {
      this.program = program
      val heights = Functions.heights(program).toSeq.sortBy(_._2).reverse
      functionData = toMap(heights.map{case (f, _) => f -> new FunctionData(f, program)})
    }

    private def handleFunction(function: ast.ProgramFunction, c: C): List[VerificationResult] = {
      val data = functionData(function)

      val resultSpecsWellDefined = checkSpecificationsWellDefined(function, c)

      if (!config.disableFunctionAxiomatization()) {
        decider.prover.assume(data.limitedAxiom)
        decider.prover.assume(data.postAxiom)
      }

      val result = verifyAndAxiomatize(function, c)

      if (!config.disableFunctionAxiomatization()) {
        decider.prover.assume(data.axiom)
      }

      resultSpecsWellDefined :: result :: Nil
    }

    private def declareFunctions() {
      functionData.values foreach {fd =>
        decider.prover.declare(FunctionDecl(fd.func))
        decider.prover.declare(FunctionDecl(fd.limitedFunc))
      }
    }

    private def checkSpecificationsWellDefined(function: ast.ProgramFunction, c: C): VerificationResult = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + " (specs well-defined) " + ("-" * 10)
      logger.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val ins = function.formalArgs.map(_.localVar)
      val out = function.result

      val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
      val σ = Σ(γ, Ø, Ø)

      val functionMalformed = FunctionNotWellformed(function)
      val data = functionData(function)
      var recorders = List[SnapshotRecorder]()

      val result =
        inScope {
          produces(σ, fresh, FullPerm(), function.pres, _ => functionMalformed, c)((σ1, c1) =>
            evals(σ1, function.posts, functionMalformed, c1)((tPosts, c2) => {
              recorders ::= c2.snapshotRecorder.get
              Success()}))}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))
        data.optLocToSnap = Some(summaryRecorder.locToSnap)
        data.optFappToSnap = Some(summaryRecorder.fappToSnap)
      }

      result
    }

    private def verifyAndAxiomatize(function: ast.ProgramFunction, c: C): VerificationResult = {
      val comment = "-" * 10 + " FUNCTION " + function.name + "-" * 10
      logger.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val ins = function.formalArgs.map(_.localVar)
      val out = function.result

      val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
      val σ = Σ(γ, Ø, Ø)

      val postError = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, function)

      val data = functionData(function)
      var recorders = List[SnapshotRecorder]()
      val pres = ast.utils.BigAnd(function.pres)

      val result =
        inScope {
          /* TODO: Instead of re-producing the precondition and, if necessary,
           *       removing the malformed function errors (which are recorded as
           *       internal errors this time), it would be better
           *       to cache and reuse the state and context yielded by producing
           *       the precondition in checkSpecificationsWellDefined.
           *       Since the precondition might branch we would have to record
           *       a sequence of (σ, c)-pairs (commit b4defbd5768e contains an
           *       implementation).
           *       However, to improve error reporting, checkSpecificationsWellDefined
           *       uses produces(function.pres) - which currently doesn't track
           *       snapshots correctly - whereas produce(BigAnd(function.pres))
           *       is used here.
           */
          produce(σ, fresh, FullPerm(), pres, Internal(pres), c)((σ1, c2) => {
            val c2a = c2.copy(snapshotRecorder = c2.snapshotRecorder.map(_.copy(currentSnap = null)))
            eval(σ1, function.exp, FunctionNotWellformed(function), c2a)((tB, c3) => {
              recorders ::= c3.snapshotRecorder.get
              val c4 = c3.copy(snapshotRecorder = None)
              consumes(σ1 \+ (out, tB), FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
                Success())})})}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))

        data.optLocToSnap = Some(summaryRecorder.locToSnap)
        data.optFappToSnap = Some(summaryRecorder.fappToSnap)
      }

      /* Ignore internal errors; the assumption is that they have already been
       * recorded while checking well-framedness of function contracts.
       */
      result match {
        case failure: Failure[ST, H, S] =>
          if (!failure.message.isInstanceOf[Internal])
            failure
          else
            Success()

        case other => other
      }
    }

    /* Lifetime */

    def start() {}

    def reset() {
      program = null
      functionData = functionData.empty
    }

    def stop() {}

    /* Debugging */

    private def show(functionData: Map[ast.ProgramFunction, FunctionData]) =
      functionData.map { case (fun, fd) => (
        fun.name,    // Function name only
//        s"${fun.name}(${fun.formalArgs.mkString(", ")}}): ${fun.typ}",    // Function name and signature
        s"${fd.getClass.getSimpleName}@${System.identityHashCode(fd)}(${fd.programFunction.name}})"
      )}
  }
}

private class HeapAccessReplacingExpressionTranslator(val symbolConverter: SymbolConvert,
                                                      fresh: (String, Sort) => Term,
                                                      limitedFunction: Function => Function)
    extends ExpressionTranslator {

  private val toSort = (typ: ast.Type, _: Any) => symbolConverter.toSort(typ)

  private var program: ast.Program = null
  private var locToSnap: Map[ast.LocationAccess, Term] = null
  private var fappToSnap: Map[ast.FuncApp, Term] = null
  private var parentFunc: ast.ProgramFunction = null
  private var resultReplacement: FApp = null
  private var ignoreAccessPredicates = false

  def translate(program: ast.Program,
                func: ast.ProgramFunction,
                locToSnap: Map[ast.LocationAccess, Term],
                fappToSnap: Map[ast.FuncApp, Term]): Term = {

    this.program = program
    this.parentFunc = func

    val body = translate(program, func.exp, locToSnap, fappToSnap)

    this.program = null
    this.parentFunc = null

    body
  }

  def translate(program: ast.Program,
                exp: ast.Expression,
                locToSnap: Map[ast.LocationAccess, Term],
                fappToSnap: Map[ast.FuncApp, Term]): Term = {

    /* Attention: This method is reentrant (via translate(_, _)), which is why we
     * can't simply set the internal fields to null before returning.
     */

    val oldProgram = this.program
    val oldLocToSnap = this.locToSnap
    val oldFappToSnap = this.fappToSnap

    this.program = program
    this.locToSnap = locToSnap
    this.fappToSnap = fappToSnap

    val term = translate(toSort)(exp)

    this.program = oldProgram
    this.locToSnap = oldLocToSnap
    this.fappToSnap = oldFappToSnap

    term
  }

  def translatePostcondition(program: ast.Program,
                             post: ast.Expression,
                             locToSnap: Map[ast.LocationAccess, Term],
                             fappToSnap: Map[ast.FuncApp, Term],
                             resultReplacement: FApp): Term = {

    this.program = program
    this.locToSnap = locToSnap
    this.fappToSnap = fappToSnap
    this.resultReplacement = resultReplacement

    val term = translate(toSort)(post)

    this.program = null
    this.locToSnap = null
    this.fappToSnap = null
    this.resultReplacement = null

    term
  }

  def translatePrecondition(program: ast.Program,
                            pre: ast.Expression,
                            locToSnap: Map[ast.LocationAccess, Term],
                            fappToSnap: Map[ast.FuncApp, Term]): Term = {

    this.program = program
    this.locToSnap = locToSnap
    this.fappToSnap = fappToSnap
    this.ignoreAccessPredicates = true

    val term = translate(toSort)(pre)

    this.program = null
    this.locToSnap = null
    this.fappToSnap = null
    this.ignoreAccessPredicates = false

    term
  }

  /* Attention: Expects some fields, e.g., `program` and `locToSnap`, to be
   * set, depending on which kind of translation is performed.
   * See public `translate` methods.
   */
  override protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort)
                                  (e: ast.Expression)
                                  : Term =

    e match {
      case loc: ast.LocationAccess => getOrFresh(locToSnap, loc, toSort(loc.typ, Map()))
      case ast.Unfolding(_, eIn) => translate(toSort)(eIn)

      case eFApp: ast.FuncApp =>
        val silverFunc = program.findFunction(eFApp.funcname)
        val pre = ast.utils.BigAnd(silverFunc.pres)

        val func = symbolConverter.toFunction(silverFunc)
        val args = eFApp.args map (arg => translate(program, arg, locToSnap, fappToSnap))

        val snap = getOrFresh(fappToSnap, eFApp, sorts.Snap)
          /* It is assumed that the entry is missing because the currently
           * translated function is malformed. In order to be able to continue
           * we use a fresh term (instead of aborting)
           */

        val fapp = FApp(func, snap, args)

        if (eFApp.func(program) == parentFunc)
          fapp.copy(function = limitedFunction(fapp.function))
        else
          fapp

      case _: ast.AccessPredicate if ignoreAccessPredicates => True()
      case _: ast.ResultLiteral => resultReplacement
      case _ => super.translate(toSort)(e)
    }

  private def getOrFresh[K](map: Map[K, Term], key: K, sort: Sort): Term = map.get(key) match {
    case Some(s) => s.convert(sort)
    case None => fresh("$unresolved", sort)
  }
}
