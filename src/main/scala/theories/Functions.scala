/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package theories

import com.weiglewilczek.slf4s.Logging
import silver.components.StatefulComponent
import silver.verifier.errors.{Internal, FunctionNotWellformed, PostconditionViolated}
import interfaces.{VerificationResult, Consumer, Producer, Evaluator, Success}
import interfaces.decider.Decider
import interfaces.state.{StateFactory, State, PathConditions, Heap, Store}
import interfaces.state.factoryUtils.Ø
import reporting.DefaultContext
import state.{SymbolConvert, DirectChunk}
import state.terms._
import state.terms.predef._

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

  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
  import decider.{fresh, inScope}

  val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  val symbolConverter: SymbolConvert

  private val expressionTranslator =
    new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh, limitedFunction)

  private class FunctionData(programFunction: ast.ProgramFunction, program: ast.Program) {
    val func = symbolConverter.toFunction(programFunction)
    val formalArgs = programFunction.formalArgs map (v => Var(v.name, symbolConverter.toSort(v.typ)))
    val args = Seq(`?s`) ++ formalArgs
    val fapp = FApp(func, `?s`, formalArgs)
    val triggers = Trigger(fapp :: Nil) :: Nil

    val limitedFunc = limitedFunction(func)

    val limitedAxiom = {
      val limFApp = FApp(limitedFunc, `?s`, formalArgs)
      Quantification(Forall, args, limFApp === fapp, triggers)
    }

    var optLocToSnap: Option[Map[ast.LocationAccess, Term]] = None
    var optFappToSnap: Option[Map[ast.FuncApp, Term]] = None

    /* If silverFunc isn't well-formed then the entries might be missing*/
    def locToSnap = optLocToSnap.getOrElse(Map[ast.LocationAccess, Term]())
    def fappToSnap = optFappToSnap.getOrElse(Map[ast.FuncApp, Term]())

    def axiom = {
      val body = expressionTranslator.translate(program, programFunction, locToSnap, fappToSnap)
      val nonNulls = True()
      //        val nonNulls = utils.BigAnd(
      //          map.collect{case (fa: ast.FieldAccess, _) => fa.rcv}
      //              .map(rcv => expressionTranslator.translate(rcv, map) !== terms.Null())
      //              .toSet[Term])
      Quantification(Forall, args, And(nonNulls, fapp === body), triggers)
    }

    def postAxiom = {
      if (programFunction.posts.nonEmpty) {
        val post = expressionTranslator.translatePostcondition(program, ast.utils.BigAnd(programFunction.posts), locToSnap, fapp)
        Quantification(Forall, args, post, triggers)
      } else
        True()
    }
  }

  private def limitedFunction(funcSymbol: Function) =
    Function(funcSymbol.id + "$", funcSymbol.sort)

  object functionsSupporter extends StatefulComponent /*extends PreambleEmitter*/ {
    private var program: ast.Program = null
//    private var collectedFunctions = Set[ast.ProgramFunction]()
    private var functionData = Map[ast.ProgramFunction, FunctionData]()

    def analyze(program: ast.Program) {
      this.program = program
      functionData = toMap(program.functions map (f => f -> new FunctionData(f, program)))
    }

    def declareFunctions() {
      functionData.values foreach {fd =>
        decider.prover.declare(FunctionDecl(fd.func))
        decider.prover.declare(FunctionDecl(fd.limitedFunc))
      }
    }

    def checkSpecificationsWellDefined(): List[VerificationResult] = {
      val c = DefaultContext(program = program, recordSnaps = true)

      functionData.keys.map(function => checkSpecificationsWellDefined(function, c)).toList
    }

    private def checkSpecificationsWellDefined(function: ast.ProgramFunction, c: C): VerificationResult = {
      val comment = ("-" * 10) + " FUNCTION " + function.name + " (specs well-defined) " + ("-" * 10)
      logger.debug(s"\n\n$comment\n")
      decider.prover.logComment(comment)

      val ins = function.formalArgs.map(_.localVar)
      val out = function.result

      val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
      val σ = Σ(γ, Ø, Ø)

//      val postError = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, function)
      val functionMalformed = FunctionNotWellformed(function)
//      val functionMalformedGenerator = (_: ast.Expression) => functionMalformed
//      val internalError = (offendingNode: ast.Expression) => Internal(offendingNode)
//      val c = DefaultContext(program = program, recordSnaps = true)
      var cs = List[C]()

      val result =
        inScope {
          produces(σ, fresh, FullPerm(), function.pres, _ => functionMalformed, c)((σ1, c1) =>
            evals(σ1, function.posts, functionMalformed, c1)((tPosts, c2) => {
              cs ::= c2
              Success()}))}

      if (cs.nonEmpty) {
        val c1 = cs.tail.foldLeft(cs.head)((cAcc, c) => cAcc.merge(c))
        val fd = functionData(function)

        fd.optLocToSnap = Some(c1.locToSnap)
        fd.optFappToSnap = Some(c1.fappToSnap)
      }

      result
    }

    def verifyAndAxiomatize(): List[VerificationResult] = {
      val c = DefaultContext(program = program, recordSnaps = true)

      functionData.keys.map(function => verifyAndAxiomatize(function, c)).toList
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
//      val malformedError = (_: ast.Expression) => FunctionNotWellformed(function)
//      val internalError = (offendingNode: ast.Expression) => Internal(offendingNode)

      val c1 = c.copy(recordSnaps = true)
      var cs = List[C]()

      val result =
        inScope {
          val pres = ast.utils.BigAnd(function.pres)
          produce(σ, fresh, FullPerm(), pres, Internal(pres), c1)((σ1, c2) => { // TODO: Reuse σ1 and c1 from checkWellDefinedness
            val c2a = c2.copy(currentSnap = None)
            eval(σ1, function.exp, FunctionNotWellformed(function), c2)((tB, c3) => {
              val c4 = c3.copy(recordSnaps = false)
              cs ::= c3
              consumes(σ1 \+ (out, tB), FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
                Success())})})}

      if (cs.nonEmpty) {
        /* The recorded data should be a superset of the data recorded while
         * checking well-definedness of function specifications.
         */

        val c1 = cs.tail.foldLeft(cs.head)((cAcc, c) => cAcc.merge(c))
        val fd = functionData(function)

        fd.optLocToSnap = Some(c1.locToSnap)
        fd.optFappToSnap = Some(c1.fappToSnap)
      }

      result
    }

//    def verifyFunctionAndPrepareAxiomatization(function: ast.ProgramFunction, c: C): VerificationResult = {
//      logger.debug("\n\n" + "-" * 10 + " FUNCTION " + function.name + "-" * 10 + "\n")
//      decider.prover.logComment("%s %s %s".format("-" * 10, function.name, "-" * 10))
//
////      println(s"\n[axiomatizeFunction] ${function.name}")
//
//      val ins = function.formalArgs.map(_.localVar)
//      val out = function.result
//
//      val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
//      val σ = Σ(γ, Ø, Ø)
//
//      val postError = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, function)
//      val malformedError = (_: ast.Expression) => FunctionNotWellformed(function)
//      val internalError = (offendingNode: ast.Expression) => Internal(offendingNode)
//
//      var cs = List[C]()
//
//      val result =
//        inScope {
//          (inScope {
//            produces(σ, fresh, FullPerm(), function.pres ++ function.posts, malformedError, c)((_, c2) =>
//              Success())}
//              &&
//              inScope {
//  //              println(s"\n--------- ---- ${function.name} ----- ---------")
//                val c1 = c // c.copy(recordAccesses = true)
//                val pres = ast.utils.BigAnd(function.pres)
//                produce(σ, fresh, FullPerm(), pres, Internal(pres), c1)((σ1, c2) => {
//  //              produces(σ, fresh, FullPerm(), function.pres, internalError, c1)((σ1, c2) =>
//                  val c2a = c2.copy(currentSnap = None)
//                  eval(σ1, function.exp, FunctionNotWellformed(function), c2)((tB, c3) => {
//  //                  println(s"\n  --- ${function.name} ---\n")
//                    val c4 = c3.copy(recordSnaps = false) // c3.copy(recordAccesses = false)
//  //                  println(s"  chunkToSnap = ${c4.chunkToSnap}")
//  //                  println(s"  locToChunk = ${c4.locToChunk}")
//  //                  println(s"  " + decider.π)
//                    //                  val locToSnap = c4.locToSnap // cc4.locToChunk.map{case (loc, ch) => loc -> c4.chunkToSnap(ch)}
//  //                  println("  locToSnap =")
//  //                  c4.locToSnap foreach {case (loc, snap) => println(s"    $loc -> $snap") }
//
//  //                  val snapRecords = funcToSnapRecords.get(function) match {
//  //                    case None => (c4.locToSnap, c4.locToSnap)
//  //                    case Some((locToSnap, fappToSnap)) =>
//  //                      val lts =
//  //                        silicon.utils.conflictFreeUnion(locToSnap, c4.locToSnap) match {
//  //                          case Right(_lts) => _lts
//  //                          case _ => sys.error("Unexpected situation while axiomatising functions")
//  //                        }
//  //                      val fts =
//  //                        silicon.utils.conflictFreeUnion(fappToSnap, c4.fappToSnap) match {
//  //                          case Right(_fts) => _fts
//  //                          case _ => sys.error("Unexpected situation while axiomatising functions")
//  //                        }
//  //
//  //                      (lts, fts)
//  //                  }
//  //
//  //                  funcToSnapRecords += function -> snapRecords
//
//                    cs ::= c3
//
//  //                  println()
//  //                  funcToLocToSnap(function) foreach println
//
//  //                  c4.locToChunk.foreach{case (loc, ch) =>
//  //                    println(s"  $loc -> ${c4.chunkToSnap(ch)}")
//  //                  }
//  //                  val termToSnap = c4.locToChunk.map{case (loc, ch) =>
//  //                    val t =  ch match {
//  //                      case fch: FieldChunk => fch.value
//  //                      case pch: PredicateChunk => pch.snap
//  //                    }
//  //
//  //                    t -> c4.chunkToSnap(ch)
//  //                  }
//  //                  //                  println(s"  tB = $tB")
//  //                  val fb = tB.replace(termToSnap)
//  //                  println(s"  fb = $fb")
//                    consumes(σ1 \+ (out, tB), FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
//                      Success())})})})}
//
//      if (cs.nonEmpty) {
//        val c1 = cs.tail.foldLeft(cs.head)((cAcc, c) => cAcc.merge(c))
//        funcToSnapRecords += function -> (c1.locToSnap, c1.fappToSnap)
//      }
//
//      result
//    }

//    private def disjointUnion[K, V](m1: Map[K, V], m2: Map[K,V], errmsg: String) = {
//      assert(m1.keys.toSet.intersect(m2.keys.toSet).isEmpty, errmsg)
//
//      m1 ++ m2
//    }

//    private def generateFunctionSymbols(program: ast.Program) {
//      collectedFunctions foreach { silverFunc =>
//        val func = symbolConverter.toFunction(silverFunc)
//        translatedFunctions += func
//
//        val vs = silverFunc.formalArgs map (v => Var(v.name, symbolConverter.toSort(v.typ)))
//        val fapp = FApp(func, `?s`, vs)
//        val trs = Seq(Trigger(Seq(fapp)))
//
//        val limFunc = limitedFunction(func)
//        translatedFunctions += limFunc
//
//        /* The axioms can only be generated after the functions have been verified
//         * because the relations between accessibility predicates occurring in the
//         * precondition and location accesses occurring in the function body (and
//         * pre/post) are recorded while the function is verified.
//         */
//
//        axiomGenerators += (() => {
//          val limFApp = FApp(limFunc, `?s`, vs)
//          val limEq = limFApp === fapp
//          val limAx = Quantification(Forall, Seq(`?s`) ++ vs, limEq, trs)
////          axioms += limAx
//
////          println(fapp.function.id)
//          val (locToSnap, fappToSnap) =
//            funcToSnapRecords.getOrElse(silverFunc, (Map[ast.LocationAccess, Term](), Map[ast.FuncApp, Term]()))
//            /* If silverFunc isn't well-formed then the entry might be missing*/
//
//          val body = expressionTranslator.translate(program, silverFunc, locToSnap, fappToSnap)
//          val nonNulls = True()
//          //        val nonNulls = utils.BigAnd(
//          //          map.collect{case (fa: ast.FieldAccess, _) => fa.rcv}
//          //              .map(rcv => expressionTranslator.translate(rcv, map) !== terms.Null())
//          //              .toSet[Term])
//          val eq = fapp === body
//          val ax = Quantification(Forall, Seq(`?s`) ++ vs, And(nonNulls, eq), trs)
////          axioms += ax
//
//          val postAx =
//            if (silverFunc.posts.nonEmpty) {
//            val post = expressionTranslator.translatePostcondition(program, ast.utils.BigAnd(silverFunc.posts), locToSnap, fapp)
//
//            //            val post = ast.utils.BigAnd(silverFunc.posts)
//            //            /* TODO: Hacky! Only works if the term-vars chosen above have the same names
//            //             *       as the formalArgs here, and if these are then later on translated into
//            //             *       term-vars w/o being renamed.
//            //             *       Possible alternatives: replace Result with term-fapp from above while
//            //             *       translating the postcondition; or translate first and then transform
//            //             *       the resulting term by replacing the term-result with the term-fapp.
//            //             */
//            //            val funcApp = ast.FuncApp(func, func.formalArgs map (_.localVar))()
//            //            val postWithApp = Expressions.instantiateVariables(post, Seq(func.result), Seq(funcApp))
//            //            val tPost = expressionTranslator.translate(postWithApp, map)
//
//            val postAx = Quantification(Forall, Seq(`?s`) ++ vs, post, trs)
//            //            axioms += postAx
//            //
//            //            val limFuncApp = ast.FuncApp(func.copy(name = func.name + "$")(func.pos, func.info), func.formalArgs map (_.localVar))()
//            //            val limPostWithApp = Expressions.instantiateVariables(post, Seq(func.result), Seq(limFuncApp))
//            //            val limTPost = expressionTranslator.translate(limPostWithApp, map)
//            //            val limTRS = Seq(terms.Trigger(Seq(limFApp)))
//            //            val limPostAx = terms.Quantification(terms.Forall, Seq(s) ++ vs, limTPost, limTRS)
//            //            axioms += limPostAx
//            postAx
//          } else
//            True()
//
//          Set(ax, postAx, limAx)
//        })
//      }
//    }

//    private def generateFunctionAxioms() {
//      collectedFunctions foreach { silverFunc =>
//        val limFApp = FApp(limFunc, `?s`, vs)
//        val limEq = limFApp === fapp
//        val limAx = Quantification(Forall, Seq(`?s`) ++ vs, limEq, trs)
//        axioms += limAx
//
//        val body = expressionTranslator.translate(silverFunc, funcToLocToSnap(silverFunc))
//        val nonNulls = True()
//        //        val nonNulls = utils.BigAnd(
//        //          map.collect{case (fa: ast.FieldAccess, _) => fa.rcv}
//        //              .map(rcv => expressionTranslator.translate(rcv, map) !== terms.Null())
//        //              .toSet[Term])
//        val eq = fapp === body
//        val ax = Quantification(Forall, Seq(`?s`) ++ vs, And(nonNulls, eq), trs)
//        axioms += ax
//      }
//    }

//    val sorts = Set[Sort]()
//
//    def declareSorts() {}

//    def symbols = Some(translatedFunctions)
//    def symbols = Some(toSet(functionData.values flatMap (fd => fd.func :: fd.limitedFunc :: Nil)))

//    private def declareSymbols() {
////      translatedFunctions foreach (func => decider.prover.declare(FunctionDecl(func)))
//      symbols map (func => decider.prover.declare(FunctionDecl(func)))
//    }

    def emitPostconditionAxioms() {
      functionData.values foreach (fd => decider.prover.assume(fd.postAxiom))
    }

    def emitOtherAxioms() {
      functionData.values foreach {fd =>
        decider.prover.assume(fd.axiom)
        decider.prover.assume(fd.limitedAxiom)
      }
    }

    /* Lifetime */

    def start() {}

    def reset() {
//      collectedFunctions = collectedFunctions.empty
//      translatedFunctions = translatedFunctions.empty
//      funcToSnapRecords = funcToSnapRecords.empty
//      axiomGenerators = axiomGenerators.empty
      functionData = functionData.empty
      program = null
    }

    def stop() {}
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

  def translate(program: ast.Program,
                func: ast.ProgramFunction,
                locToSnap: Map[ast.LocationAccess, Term],
                fappToSnap: Map[ast.FuncApp, Term]): Term = {

//    val oldProgram = this.program
//    val oldParentFunc = parentFunc

    this.program = program
    this.parentFunc = func

    val body = translate(program, func.exp, locToSnap, fappToSnap)

    this.program = null
    this.parentFunc = null

//    this.program = oldProgram
//    this.parentFunc = oldParentFunc

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
                             resultReplacement: FApp): Term = {

    this.program = program
    this.locToSnap = locToSnap
    this.resultReplacement = resultReplacement

    val term = translate(toSort)(post)

    this.program = null
    this.locToSnap = null
    this.resultReplacement = null

    term
  }

  /* Attention: Expects `locToSnap`, `parentFunc` and `program` to be set, see
   * public `translate` methods.
   */
  override protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort)
                                  (e: ast.Expression)
                                  : Term =

    e match {
      case loc: ast.LocationAccess =>
//        println(s"$loc -> ${locToSnap(loc)}")
//        println(s"loc = $loc")
//        println(s"locToSnap(loc) = $locToSnap(loc)")
//        println(s"locToSnap = $locToSnap")
//        val sort = toSort(loc.typ, Map())

        val snap = getOrFresh(locToSnap, loc, toSort(loc.typ, Map()))
//        val snap = locToSnap.get(loc) match {
//          case None =>
//            /* It is assumed that the entry is missing because the currently
//             * translated function is malformed. In order to be able to continue
//             * we use a fresh term (instead of aborting)
//             */
//            fresh("$unresolved", sort)
//
//          case Some(s) =>
//            s.convert(sort)
//        }

        snap

      case ast.Unfolding(_, eIn) =>
//        assert(accs contains predloc, s"Cannot statically determine to which access predicate $predloc belongs. Known are ${accs.keys})")
//        accToSnapMapping(predloc.predicateBody, accs(predloc), accs)
        translate(toSort)(eIn)

      case eFApp: ast.FuncApp =>
        val silverFunc = program.findFunction(eFApp.funcname)
        val pre = ast.utils.BigAnd(silverFunc.pres)
//        val snap = accToSnapTerm(pre, accs)

        val func = symbolConverter.toFunction(silverFunc)
        val args = eFApp.args map (arg => translate(program, arg, locToSnap, fappToSnap))

        val snap = getOrFresh(fappToSnap, eFApp, sorts.Snap)
          /* It is assumed that the entry is missing because the currently
           * translated function is malformed. In order to be able to continue
           * we use a fresh term (instead of aborting)
           */

//        val snap = fappToSnap.get(eFApp) match {
//          case None =>
//
//            fresh("$unresolved", sorts.Snap)
//
//          case Some(s) =>
//            s.convert(sorts.Snap)
//        }

        val fapp = FApp(func, snap, args)
//        println(s"\nfapp = $fapp")
//        println(s"parentFunc = ${parentFunc.name}")
//        println(s"eFApp = ${eFApp.funcname}")
//        println(eFApp.func(program) == parentFunc)
//        val tFApp = translateFuncApp(eFApp, snap, accs)

        if (eFApp.func(program) == parentFunc)
          fapp.copy(function = limitedFunction(fapp.function))
        else
          fapp

      case _: ast.ResultLiteral => resultReplacement

      case _ => super.translate(toSort)(e)
    }

  private def getOrFresh[K](map: Map[K, Term], key: K, sort: Sort): Term = map.get(key) match {
    case Some(s) => s.convert(sort)
    case None => fresh("$unresolved", sort)
  }
}
