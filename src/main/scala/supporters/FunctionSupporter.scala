/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.ast
import silver.ast.utility.Functions
import silver.components.StatefulComponent
import silver.verifier.errors.{Internal, PostconditionViolated, FunctionNotWellformed}
import interfaces.{VerificationResult, Success, Failure, Producer, Consumer, Evaluator}
import interfaces.decider.Decider
import interfaces.state.{State, StateFactory, PathConditions, Heap, Store, Mergeable}
import interfaces.state.factoryUtils.Ø
import state.{SymbolConvert, DirectChunk, DefaultContext}
import state.terms.{utils => _, _}
import state.terms.predef.`?s`

case class SnapshotRecorder(private val locToSnaps: Map[ast.LocationAccess, Set[(Stack[Term], Term)]] = Map(),
                            private val fappToSnaps: Map[ast.FuncApp, Set[(Stack[Term], Term)]] = Map())
    extends Mergeable[SnapshotRecorder]
       with Logging {

  def locToSnap: Map[ast.LocationAccess, Term] = {
    locToSnaps.map { case (loc, guardsToSnap) =>
      /* We (arbitrarily) make the snap of the head pair (guards -> snap) of
       * guardsToSnap the inner-most else-clause, i.e., we drop the guards.
       */
      val conditionalSnap =
        guardsToSnap.tail.foldLeft(guardsToSnap.head._2) { case (tailSnap, (guards, snap)) =>
          Ite(And(guards.toSet), snap, tailSnap)
        }

      loc -> conditionalSnap
    }
  }

  def fappToSnap: Map[ast.FuncApp, Term] = {
    fappToSnaps.map { case (fapp, guardsToSnap) =>
      /* We (arbitrarily) make the snap of the head pair (guards -> snap) of
       * guardsToSnap the inner-most else-clause, i.e., we drop the guards.
       */
      val conditionalSnap =
        guardsToSnap.tail.foldLeft(guardsToSnap.head._2) { case (tailSnap, (guards, snap)) =>
          Ite(And(guards.toSet), snap, tailSnap)
        }

      fapp -> conditionalSnap
    }
  }

  def recordSnapshot(loc: ast.LocationAccess, guards: Stack[Term], snap: Term) = {
    val guardsToSnaps = locToSnaps.getOrElse(loc, Set()) + (guards -> snap)
    copy(locToSnaps = locToSnaps + (loc -> guardsToSnaps))
  }

  def recordSnapshot(fapp: ast.FuncApp, guards: Stack[Term], snap: Term) = {
    val guardsToSnaps = fappToSnaps.getOrElse(fapp, Set()) + (guards -> snap)
    copy(fappToSnaps = fappToSnaps + (fapp -> guardsToSnaps))
  }

  def merge(other: SnapshotRecorder): SnapshotRecorder = {
    val lts =
      other.locToSnaps.foldLeft(locToSnaps){case (accLts, (loc, guardsToSnaps)) =>
        val guardsToSnaps1 = accLts.getOrElse(loc, Set()) ++ guardsToSnaps
        accLts + (loc -> guardsToSnaps1)
      }

    val fts =
      other.fappToSnaps.foldLeft(fappToSnaps){case (accFts, (fapp, guardsToSnaps)) =>
        val guardsToSnaps1 = accFts.getOrElse(fapp, Set()) ++ guardsToSnaps
        accFts + (fapp -> guardsToSnaps1)
      }

    copy(locToSnaps = lts, fappToSnaps = fts)
  }

  /** Tries to merge two snapshots. For two snapshots to be mergable, they have
    * to be structurally equivalent, exception if one sub-snapshot is `Unit`,
    * in which case the corresponding sub-snapshot of the other snapshot can be
    * any snapshot. In this case, the resulting snapshot will contain the
    * non-`Unit` sub-snapshot.
    *
    * For example,
    *   `Combine(Second(First(s)), Unit)` and
    *   `Combine(Second(First(s)), Second(s))`
    * can be merged, yielding
    *   `Combine(Second(First(s)), Second(s))`
    * and
    *   `Combine(Second(First(s)), Unit)` and
    *   `Combine(Second(Unit), Second(s))`
    * can as well (but should never occur in practice), yielding
    *   `Combine(Second(First(s)), Second(s))`
    * but
    *   `Combine(Second(First(s)), Second(s))` and
    *   `Combine(First(First(s)), Second(s))`
    * cannot.
    *
    * @param t1 First snapshot to merge.
    * @param t2 Second snapshot to merge.
    * @return If `t1` and `t2` can be merged, then `Some(t3)`, where `t3` is
    *         the resulting snapshot. `None` otherwise.
    */
  private def mergeSnapshots(t1: Term, t2: Term): Option[Term] = {
    assert(t1.sort == sorts.Snap && t2.sort == sorts.Snap,
           s"Expected both terms to be of sort Snap, but found ${t1.sort}, ${t2.sort}")

    def merge(t1: Term, t2: Term): Option[Term] = (t1, t2) match {
      case (`t1`, `t1`) => Some(t1)
      case (Unit, _) => Some(t2)
      case (_, Unit) => Some(t1)
      case (First(t11), First(t21)) => merge(t11, t21).map(First)
      case (Second(t11), Second(t21)) => merge(t11, t21).map(Second)
      case (Combine(t11, t12), Combine(t21, t22)) =>
        merge(t11, t21).fold(None: Option[Term])(t13 => merge(t12, t22).map(t23 => Combine(t13, t23)))
      case _ => None
    }

    merge(t1, t2)
  }

  override lazy val toString = {
    val ltsStrs = locToSnaps map {case (k, v) => s"$k  |==>  $v"}
    val ftsStrs = fappToSnap map {case (k, v) => s"$k  |==>  $v"}

    s"""SnapshotRecorder(
       |  locToSnaps:
       |    ${ltsStrs.mkString("\n    ")}
       |  fappToSnap:
       |    ${ftsStrs.mkString("\n    ")}
       |)
     """.stripMargin
  }
}

class FunctionData(val programFunction: ast.Function,
                   val height: Int,
                   val program: ast.Program,
                   val symbolConverter: SymbolConvert,
                   val expressionTranslator: HeapAccessReplacingExpressionTranslator,
                   fresh: ast.LocalVar => Var) {

  val func = symbolConverter.toFunction(programFunction)

  //    val formalArgs = programFunction.formalArgs map (v => Var(v.name, symbolConverter.toSort(v.typ)))
  val formalArgs: Map[ast.AbstractLocalVar, Var] =
    toMap(programFunction.formalArgs.map(_.localVar).map(v => v -> fresh(v)))

  val args = Seq(`?s`) ++ formalArgs.values

  val fapp = FApp(func, `?s`, formalArgs.values.toSeq)
  val triggers = Trigger(fapp :: Nil) :: Nil

  val limitedFunc = func.limitedVersion
  val limitedFapp = FApp(limitedFunc, `?s`, formalArgs.values.toSeq)
  val limitedTriggers = Trigger(limitedFapp :: Nil) :: Nil

  val limitedAxiom = {
    val limFApp = FApp(limitedFunc, `?s`, formalArgs.values.toSeq)

    Quantification(Forall, args, limFApp === fapp, triggers)
  }

  var welldefined = false

  /* If the program function isn't well-formed, the following field might remain empty */
  private var optLocToSnap: Option[Map[ast.LocationAccess, Term]] = None
  private var optFappToSnap: Option[Map[ast.FuncApp, Term]] = None

  def locToSnap = optLocToSnap.getOrElse(Map[ast.LocationAccess, Term]())
  def fappToSnap = optFappToSnap.getOrElse(Map[ast.FuncApp, Term]())

  def locToSnap_=(lts: Map[ast.LocationAccess, Term]) { optLocToSnap = Some(lts) }
  def fappToSnap_=(fts: Map[ast.FuncApp, Term]) { optFappToSnap = Some(fts) }

  lazy val translatedPre: Option[Term] = {
    val pre = utils.ast.BigAnd(programFunction.pres)

    expressionTranslator.translatePrecondition(program, pre, this)
  }

  lazy val axiom: Option[Term] = translatedPre match {
    case None => None
    case Some(pre) =>
      val optBody = expressionTranslator.translate(program, programFunction, this)

      /* TODO: We may only add non-null assumptions about receivers that are
       * definitely dereferenced inside functions. That is, the receivers of
       * field accesses that occur under a conditional may not be assumed to
       * be non-null!
       */
      //      val nonNulls = And(
      //        programFunction.exp.deepCollect{case fa: ast.FieldAccess => fa.rcv}
      //                           .map(rcv => expressionTranslator.translate(program, rcv, locToSnap, fappToSnap) !== Null())
      //                           .distinct: _*)
      optBody.map(body =>
        Quantification(Forall, args, Implies(pre, And(fapp === body/*, nonNulls*/)), triggers))
  }

  lazy val postAxiom: Option[Term] = translatedPre match {
    case None => None
    case Some(pre) =>
      if (programFunction.posts.nonEmpty) {
        val post = utils.ast.BigAnd(programFunction.posts)

        val optPost =
          expressionTranslator.translatePostcondition(program, post, this)

        optPost.map(post =>
          Quantification(Forall, args, Implies(pre, post), limitedTriggers))
      } else
        Some(True())
  }
}

trait FunctionSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext]
            with Producer[ST, H, S, DefaultContext]
            with Consumer[DirectChunk, ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type AxiomGenerator = () => Quantification

  val config: Config

  val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, inScope}

  val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  val symbolConverter: SymbolConvert

  private val expressionTranslator =
    new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh)

  object functionsSupporter extends StatefulComponent {
    private var program: ast.Program = null

    private var functionData = Map[ast.Function, FunctionData]()

    def handleFunctions(program: ast.Program): List[VerificationResult] =  {
      reset()
      analyze(program)

      decider.prover.logComment("-" * 60)
      decider.prover.logComment("Declaring program functions")
      decider.prover.declare(VarDecl(`?s`))
      declareFunctions()

      val c = DefaultContext(program = program, snapshotRecorder = Some(SnapshotRecorder()))

      functionData.keys.flatMap(function => handleFunction(function, c)).toList
    }

    private def analyze(program: ast.Program) {
      this.program = program

      val heights = Functions.heights(program).toSeq.sortBy(_._2).reverse

      functionData = toMap(
        heights.map{case (func, height) =>
          val data = new FunctionData(func, height, program, symbolConverter, expressionTranslator, fresh)
          func -> data})

      /* TODO: FunctionData and HeapAccessReplacingExpressionTranslator depend
       *       on each other. Refactor s.t. this delayed assignment is no
       *       longer needed.
       */
      expressionTranslator.functionData = functionData
    }

    private def handleFunction(function: ast.Function, c: C): List[VerificationResult] = {
      val data = functionData(function)

      val resultSpecsWellDefined = checkSpecificationsWellDefined(function, c)

      decider.prover.assume(data.limitedAxiom)
      data.postAxiom map decider.prover.assume

      val result = verifyAndAxiomatize(function, c)

      data.axiom map decider.prover.assume

      resultSpecsWellDefined :: result :: Nil
    }

    private def declareFunctions() {
      functionData.values foreach {fd =>
        decider.prover.declare(FunctionDecl(fd.func))
        decider.prover.declare(FunctionDecl(fd.limitedFunc))
      }
    }

    private def checkSpecificationsWellDefined(function: ast.Function, c: C): VerificationResult = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + " (specs well-defined) " + ("-" * 10)
      logger.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      SymbExLogger.mpf_insert(function, Σ(Ø, Ø, Ø))

      val data = functionData(function)
      val out = function.result

      val γ = Γ(data.formalArgs + (out -> fresh(out)))
      val σ = Σ(γ, Ø, Ø)

      val functionMalformed = FunctionNotWellformed(function)
      val pres = utils.ast.BigAnd(function.pres)

      /* Recording function data in this phase is necessary for generating the
       * post-axiom fpr each function. Consider a function f(x) with precondition
       * P ≡ acc(x.f) && x.f > 0 and with postcondition Q ≡ result < 0.
       * The corresponding post-axiom will be
       *   forall s,x :: P[x.f |-> s] ==> Q[result |-> f(s,x), x.f |-> s]
       * We therefore need to be able to map field accesses to the corresponding
       * snapshot accesses.
       */
      var recorders = List[SnapshotRecorder]()

      val result =
        inScope {
//          produces(σ, data.snapshot, FullPerm(), function.pres, _ => functionMalformed, c)((σ1, c1) =>
          produce(σ, sort => `?s`.convert(sort), FullPerm(), pres, functionMalformed, c)((σ1, c1) =>
            evals(σ1, function.posts, functionMalformed, c1)((tPosts, c2) => {
              recorders ::= c2.snapshotRecorder.get
              Success()}))}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))
        data.locToSnap = summaryRecorder.locToSnap
        data.fappToSnap = summaryRecorder.fappToSnap
      }

      data.welldefined = !result.isFatal

      result
    }

    private def verifyAndAxiomatize(function: ast.Function, c: C): VerificationResult = {
      val comment = "-" * 10 + " FUNCTION " + function.name + "-" * 10
      logger.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val data = functionData(function)
      val out = function.result

      val γ = Γ(data.formalArgs + (out -> fresh(out)))
      val σ = Σ(γ, Ø, Ø)

      val postError = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, function)
      val pres = utils.ast.BigAnd(function.pres)

      var recorders = List[SnapshotRecorder]()

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
           *       is used here (because it has to match DefaultEvaluator, which
           *       uses the BigAnd-version as well).
           */
          produce(σ, sort => `?s`.convert(sort), FullPerm(), pres, Internal(pres), c)((σ1, c2) =>
            function.body match {
              case None =>
                recorders ::= c2.snapshotRecorder.get
                Success()
              case Some(body) =>
                eval(σ1, body, FunctionNotWellformed(function), c2)((tB, c3) => {
                  recorders ::= c3.snapshotRecorder.get
                  val c4 = c3.copy(snapshotRecorder = None)
                  consumes(σ1 \+ (out, tB), FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
                    Success())})})}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))

        data.locToSnap = summaryRecorder.locToSnap
        data.fappToSnap = summaryRecorder.fappToSnap
      }

      data.welldefined &&= !result.isFatal

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

    private def show(functionData: Map[ast.Function, FunctionData]) =
      functionData.map { case (fun, fd) => (
        fun.name,    // Function name only
//        s"${fun.name}(${fun.formalArgs.mkString(", ")}}): ${fun.typ}",    // Function name and signature
        s"${fd.getClass.getSimpleName}@${System.identityHashCode(fd)}(${fd.programFunction.name}})"
      )}
  }
}

class HeapAccessReplacingExpressionTranslator(val symbolConverter: SymbolConvert,
                                              fresh: (String, Sort) => Var)
    extends ExpressionTranslator
       with Logging {

  private val toSort = (typ: ast.Type, _: Any) => symbolConverter.toSort(typ)

  private var program: ast.Program = null
  private var func: ast.Function = null
  private var data: FunctionData = null
  private var ignoreAccessPredicates = false
  private var failed = false

  var functionData: Map[ast.Function, FunctionData] = null

  def translate(program: ast.Program,
                func: ast.Function,
                data: FunctionData)
               : Option[Term] = {

    this.func = func
    this.program = program
    this.data = data
    this.failed = false

    val result = func.body map translate

    if (failed) None else result
  }

  private def translate(exp: ast.Exp): Term = {
    /* Attention: This method is reentrant (via private translate) */
    translate(toSort)(exp)
  }

  def translatePostcondition(program: ast.Program,
                             post: ast.Exp,
                             data: FunctionData)
                            : Option[Term] = {

    this.program = program
    this.data = data
    this.failed = false

    val result = translate(toSort)(post)

    if (failed) None else Some(result)
  }

  def translatePrecondition(program: ast.Program,
                            pre: ast.Exp,
                            data: FunctionData)
                           : Option[Term] = {

    this.program = program
    this.data = data
    this.ignoreAccessPredicates = true
    this.failed = false

    val result = translate(toSort)(pre)

    if (failed) None else Some(result)
  }

  /* Attention: Expects some fields, e.g., `program` and `locToSnap`, to be
   * set, depending on which kind of translation is performed.
   * See public `translate` methods.
   */
  override protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort)
                                  (e: ast.Exp)
                                  : Term =

    e match {
      case _: ast.Result => data.limitedFapp

      case v: ast.AbstractLocalVar =>
        data.formalArgs.get(v) match {
          case Some(t) => t
          case None => super.translate(toSort)(v)
        }

      case loc: ast.LocationAccess => getOrRecordFailure(data.locToSnap, loc, toSort(loc.typ, Map()))
      case ast.Unfolding(_, eIn) => translate(toSort)(eIn)

      case eFApp: ast.FuncApp =>
        val silverFunc = program.findFunction(eFApp.funcname)
        val pre = utils.ast.BigAnd(silverFunc.pres)
        val func = symbolConverter.toFunction(silverFunc)
        val args = eFApp.args map (arg => translate(arg))
        val snap = getOrRecordFailure(data.fappToSnap, eFApp, sorts.Snap)
        val fapp = FApp(func, snap, args)

        val callerHeight = data.height
        val calleeHeight = functionData(eFApp.func(program)).height

        if (callerHeight < calleeHeight)
          fapp
        else
          fapp.copy(function = fapp.function.limitedVersion)

      case _: ast.AccessPredicate if ignoreAccessPredicates => True()
      case q: ast.Forall if !q.isPure && ignoreAccessPredicates => True()
      case _ => super.translate(toSort)(e)
    }

  private def getOrRecordFailure[K <: ast.Positioned](map: Map[K, Term], key: K, sort: Sort): Term =
    map.get(key) match {
      case Some(s) =>
        s.convert(sort)
      case None =>
        failed = true
        if (data.welldefined) {
          println(s"Could not resolve $key (${key.pos}}) during function axiomatisation")
          logger.warn(s"Could not resolve $key (${key.pos}}) during function axiomatisation")
        }

        Var("$unresolved", sort)
    }
}
