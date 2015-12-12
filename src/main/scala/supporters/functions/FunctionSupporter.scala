/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.ast.utility.Functions
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors.{Internal, PostconditionViolated, ContractNotWellformed, FunctionNotWellformed}
import viper.silicon.supporters.{PredicateData, PredicateSupporter}
import viper.silicon.{Map, toSet}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.interfaces._
import viper.silicon.{Config, Stack, toMap}
import viper.silicon.interfaces.state._
import viper.silicon.state.{DefaultContext, SymbolConvert}
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`

class FunctionData(val programFunction: ast.Function,
                   val height: Int,
                   val program: ast.Program,
                   val symbolConverter: SymbolConvert,
                   val expressionTranslator: HeapAccessReplacingExpressionTranslator,
                   fresh: ast.LocalVar => Var,
                   predicateData: Map[ast.Predicate, PredicateData]) {

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
    val limFApp = limitedFapp//FApp(limitedFunc, `?s`, formalArgs.values.toSeq)

    Quantification(Forall, args, limFApp === fapp, triggers)
  }

  var welldefined = false

  /* If the program function isn't well-formed, the following field might remain empty */
  private var optLocToSnap: Option[Map[ast.LocationAccess, Term]] = None
  private var optFappToSnap: Option[Map[ast.FuncApp, Term]] = None
  private var optQPTerms: Option[Set[(Seq[Var], Stack[Term], Iterable[Term])]] = None
  private var optFreshFvfs: Option[Set[(ast.Field, Var)]] = None

  /* TODO: Should be lazy vals, not methods */

  def locToSnap = optLocToSnap.getOrElse(Map[ast.LocationAccess, Term]())
  def fappToSnap = optFappToSnap.getOrElse(Map[ast.FuncApp, Term]())
  def freshFvfs = optFreshFvfs.getOrElse(Set[(ast.Field, Var)]())

  def qpTerms: Iterable[Term] = optQPTerms match {
    case Some(qpts) =>
      qpts.map { case (qvars, guards, ts) =>
        val body = Implies(And(guards), And(ts))
        val additionalQVars = qvars filterNot args.contains

        if (additionalQVars.isEmpty) body
        else Forall(additionalQVars, body, Seq[Trigger]()).autoTrigger }
              /* TODO: Could use TriggerGenerator.generateFirstTriggers here */

    case None =>
      Nil
  }

  def locToSnap_=(lts: Map[ast.LocationAccess, Term]) { optLocToSnap = Some(lts) }
  def fappToSnap_=(fts: Map[ast.FuncApp, Term]) { optFappToSnap = Some(fts) }

  def freshFvfs_=(fvfs: Set[(ast.Field, Term)]) = {
    assert(fvfs.forall(_._2.isInstanceOf[Var]))
    optFreshFvfs = Some(fvfs.asInstanceOf[Set[(ast.Field, Var)]])
  }

  def qpTerms_=(qpts: Set[(Seq[Var], Stack[Term], Iterable[Term])]) { optQPTerms = Some(qpts) }

  lazy val translatedPre: Option[Term] =
    expressionTranslator.translatePrecondition(program, programFunction.pres, this)
                        .map(And)

  lazy val afterRelations: Set[Term] = translatedPre match {
    case None => Set.empty
    case Some(_) =>
      var lastFVF = freshFvfs.map{case (field, fvf) =>
        val fvfTOP = Var(s"fvfTOP_${field.name}", fvf.sort)
        field -> fvfTOP
      }.toMap

      val afters: Set[Term] =
      freshFvfs.map{case (field, freshFvf) =>
        val fvf = lastFVF(field)
        val after = FvfAfterRelation(field.name, freshFvf, fvf)

        lastFVF = lastFVF.updated(field, freshFvf)

        after
      }

      afters
  }

  lazy val definitionalAxiom: Option[Term] = translatedPre match {
    case None => None
    case Some(pre) =>
//      println("\n[definitionalAxiom]")
//      println(s"  name = ${programFunction.name}")

      val optBody = expressionTranslator.translate(program, programFunction, this)

      val predicateTriggers = predicateTriggerFApps.values
//      println(s"  predicateTriggers = ${predicateTriggers.toList}")

      /* TODO: We may only add non-null assumptions about receivers that are
       * definitely dereferenced inside functions. That is, the receivers of
       * field accesses that occur under a conditional may not be assumed to
       * be non-null!
       */
      //      val nonNulls = And(
      //        programFunction.exp.deepCollect{case fa: ast.FieldAccess => fa.rcv}
      //                           .map(rcv => expressionTranslator.translate(program, rcv, locToSnap, fappToSnap) !== Null())
      //                           .distinct: _*)
      optBody.map(translatedBody => {
        val innermostBody = And(afterRelations ++ qpTerms ++ List(Implies(pre, And(fapp === translatedBody/*, nonNulls*/))))
        val body =
          if (freshFvfs.isEmpty) innermostBody
          else Exists(freshFvfs.map(_._2), innermostBody, Nil) // TODO: Triggers?
        val allTriggers = triggers ++ (predicateTriggers map (pt => Trigger(Seq(triggerFApp, pt))))
        Forall(args, body, allTriggers)})
  }

  lazy val postAxiom: Option[Term] = translatedPre match {
    case None => None
    case Some(pre) =>
      if (programFunction.posts.nonEmpty) {
        val optPosts =
          expressionTranslator.translatePostcondition(program, programFunction.posts, this)

        optPosts.map(posts => {
          val innermostBody = And(afterRelations ++ qpTerms ++ List(Implies(pre, And(posts))))
          val body =
            if (freshFvfs.isEmpty) innermostBody
            else Exists(freshFvfs.map(_._2), innermostBody, Nil) // TODO: Triggers?
          Forall(args, body, limitedTriggers)})
      } else
        Some(True())
  }

  lazy val triggerFunc = Function(s"${func.id}%trigger", func.sort.from.tail, sorts.Bool)
  lazy val triggerFApp = Apply(triggerFunc, formalArgs.values.toSeq)

  val triggerAxiom = {
    val fapp = triggerFApp

    Quantification(Forall, args, fapp, limitedTriggers)
  }

  private[this] var predaccs: Seq[(ast.PredicateAccess, ast.Predicate)] = Vector.empty

  lazy val predicateTriggerFApps: Map[ast.Predicate, FApp] = {
    val recursiveCallsAndUnfoldings: Seq[(ast.FuncApp, Seq[ast.Unfolding])] =
      Functions.recursiveCallsAndSurroundingUnfoldings(programFunction)

//    println("  [predicateTriggers]")
//    println(s"    recursiveCallsAndUnfoldings = $recursiveCallsAndUnfoldings")

    val outerUnfoldings: Seq[ast.Unfolding] =
      recursiveCallsAndUnfoldings.flatMap(_._2.headOption)

//    println(s"    outerUnfoldings = $outerUnfoldings")

    val predicateAccesses: Seq[ast.PredicateAccess] =
      if (recursiveCallsAndUnfoldings.isEmpty)
        programFunction.pres flatMap (pre =>
          pre.shallowCollect { case predacc: ast.PredicateAccess => predacc })
      //                            .map(predacc => predicateTrigger(predacc))
      else
        outerUnfoldings map (_.acc.loc)
    //          case ast.Unfolding(ast.PredicateAccessPredicate(predacc: ast.PredicateAccess, perm), exp) =>
    //            predicateTrigger(predacc)
    //        }

//    println(s"    predicateAccesses = $predicateAccesses")

    val map: Map[ast.Predicate, FApp] = toMap(
      predicateAccesses.map(predacc => {
        val predicate = program.findPredicate(predacc.predicateName)
        val triggerFunction = predicateData(predicate).triggerFunction
        //        val triggerFunction = Function(s"${predicate.name}%trigger", args map (_.sort), sorts.Bool)

//        predaccs = predaccs :+ (predacc -> predicate)

        /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
        val args =
          expressionTranslator.translatePrecondition(program, predacc.args, this).get

//        val triggerFunction = predicateTriggers(predicate)
        //      Function(s"${predicate.name}%trigger", args map (_.sort), sorts.Bool)
        //
        //    println(s"    triggerFunction = $triggerFunction")
        //    println(s"    predacc = $predacc")
        //    println(s"    locToSnap = $locToSnap")

        val fapp =
          FApp(triggerFunction,
               expressionTranslator.getOrFail(locToSnap, predacc, sorts.Snap, programFunction.name),
               args)

        predicate -> fapp
      }))

//    println(s"    map = $map")

//    map

//    val map: Map[ast.Predicate, FApp] = toMap(
//      predaccs.map { case (predacc, pred) => pred -> predicateTriggerFApp(pred, predacc) })

//    println(s"    map = $map")

    map
  }

//  /* NOTE: Only ever call after def predicateTriggers */
//  private def predicateTriggerFApp(predicate: ast.Predicate, predacc: ast.PredicateAccess): FApp = {
//    /* TODO: Don't use translatePrecondition - refactor expressionTranslator */
//    val args =
//      expressionTranslator.translatePrecondition(program, predacc.args, this).get
//
//    val triggerFunction = predicateTriggers(predicate)
////      Function(s"${predicate.name}%trigger", args map (_.sort), sorts.Bool)
////
////    println(s"    triggerFunction = $triggerFunction")
////    println(s"    predacc = $predacc")
////    println(s"    locToSnap = $locToSnap")
//
//    FApp(triggerFunction,
//         FunctionSupporter.getOrFail(locToSnap, predacc, sorts.Snap, programFunction.name),
//         args)
//  }
}

trait FunctionSupporter[ST <: Store[ST],
                        H <: Heap[H],
                        PC <: PathConditions[PC],
                        S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[Chunk, ST, H, S, DefaultContext[H]]
            with PredicateSupporter[ST, H, PC, S] =>

  private type C = DefaultContext[H]
  private type AxiomGenerator = () => Quantification

  val config: Config
  val decider: Decider[ST, H, PC, S, C]
  val stateFactory: StateFactory[ST, H, S]
  val symbolConverter: SymbolConvert

  import decider.{fresh, inScope}
  import stateFactory._

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

      // FIXME: A workaround for Silver issue #94.
      // toList must be before flatMap. Otherwise Set will be used internally and some
      // error messages will be lost.
      functionData.keys.toList.flatMap(function => handleFunction(function))
    }

    private def analyze(program: ast.Program) {
      this.program = program

      val heights = Functions.heights(program).toSeq.sortBy(_._2).reverse

      functionData = toMap(
        heights.map{case (func, height) =>
          val data = new FunctionData(func, height, program, symbolConverter, expressionTranslator, fresh, predicateSupporter.data)
          func -> data})

      /* TODO: FunctionData and HeapAccessReplacingExpressionTranslator depend
       *       on each other. Refactor s.t. this delayed assignment is no
       *       longer needed.
       */
      expressionTranslator.functionData = functionData
    }

    private def handleFunction(function: ast.Function): List[VerificationResult] = {
      val data = functionData(function)
      val quantifiedFields = toSet(ast.utility.QuantifiedPermissions.quantifiedFields(function, program))
      val c = DefaultContext[H](program = program,
                                qpFields = quantifiedFields,
                                quantifiedVariables = data.args,
                                functionRecorder = ActualFunctionRecorder())

      val resultSpecsWellDefined = checkSpecificationsWellDefined(function, c)

      decider.prover.assume(data.limitedAxiom)
      decider.prover.assume(data.triggerAxiom)
      data.postAxiom foreach decider.prover.assume

      val result = verifyAndAxiomatize(function, c)

      data.afterRelations foreach decider.prover.assume
      data.definitionalAxiom foreach decider.prover.assume

      resultSpecsWellDefined :: result :: Nil
    }

    private def declareFunctions() {
      functionData.values foreach {fd =>
        decider.prover.declare(FunctionDecl(fd.func))
        decider.prover.declare(FunctionDecl(fd.limitedFunc))
        decider.prover.declare(FunctionDecl(fd.triggerFunc))
      }
    }

    private def checkSpecificationsWellDefined(function: ast.Function, c: C): VerificationResult = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + " (specs well-defined) " + ("-" * 10)
      log.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val data = functionData(function)
      val out = function.result

      val γ = Γ(data.formalArgs + (out -> fresh(out)))
      val σ = Σ(γ, Ø, Ø)

      /* Recording function data in this phase is necessary for generating the
       * post-axiom fpr each function. Consider a function f(x) with precondition
       * P ≡ acc(x.f) && x.f > 0 and with postcondition Q ≡ result < 0.
       * The corresponding post-axiom will be
       *   forall s,x :: P[x.f |-> s] ==> Q[result |-> f(s,x), x.f |-> s]
       * We therefore need to be able to map field accesses to the corresponding
       * snapshot accesses.
       */
      var recorders = List[FunctionRecorder]()

      val result: VerificationResult =
        inScope {
          produces(σ, sort => `?s`.convert(sort), FullPerm(), function.pres, ContractNotWellformed, c)((σ1, c1) =>
            evals(σ1, function.posts, ContractNotWellformed, c1)((tPosts, c2) => {
              recorders ::= c2.functionRecorder
              Success()}))}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))
        data.locToSnap = summaryRecorder.locToSnap
        data.fappToSnap = summaryRecorder.fappToSnap
        data.qpTerms = summaryRecorder.qpTerms
        data.freshFvfs = summaryRecorder.freshFvfs
      }

      data.welldefined = !result.isFatal

      result
    }

    private def verifyAndAxiomatize(function: ast.Function, c: C): VerificationResult = {
      val comment = "-" * 10 + " FUNCTION " + function.name + "-" * 10
      log.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val data = functionData(function)
      val out = function.result
      val tOut = fresh(out)
      val γ = Γ(data.formalArgs + (out -> tOut))
      val σ = Σ(γ, Ø, Ø)

      val postError = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, function)

      var recorders = List[FunctionRecorder]()

      val result =
        inScope {
          /* TODO: Re-use information from the first phase (i.e. from checkSpecificationsWellDefined)*/
          produces(σ, sort => `?s`.convert(sort), FullPerm(), function.pres, Internal, c)((σ1, c2) =>
            function.body match {
              case None =>
                recorders ::= c2.functionRecorder
                Success()
              case Some(body) =>
                eval(σ1, body, FunctionNotWellformed(function), c2)((tBody, c3) => {
                  recorders ::= c3.functionRecorder
                  val c4 = c3.copy(functionRecorder = NoopFunctionRecorder)
                  decider.assume(tOut === tBody)
                  consumes(σ1, FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
                    Success())})})}

      if (recorders.nonEmpty) {
        val summaryRecorder = recorders.tail.foldLeft(recorders.head)((rAcc, r) => rAcc.merge(r))

        data.locToSnap = summaryRecorder.locToSnap
        data.fappToSnap = summaryRecorder.fappToSnap
        data.qpTerms = summaryRecorder.qpTerms
        data.freshFvfs = summaryRecorder.freshFvfs
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
