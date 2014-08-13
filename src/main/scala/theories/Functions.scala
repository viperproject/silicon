/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package theories

import com.weiglewilczek.slf4s.Logging
import silver.verifier.errors.{Internal, FunctionNotWellformed, PostconditionViolated}
import interfaces.{VerificationResult, Consumer, Producer, Evaluator, PreambleEmitter, Success}
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

  val decider: Decider[DefaultFractionalPermissions, ST, H, PC, S, C]
  import decider.{fresh, inScope}

  val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  val symbolConverter: SymbolConvert

  private val expressionTranslator =
    new HeapAccessReplacingExpressionTranslator(symbolConverter, fresh, functionsSupporter.limitedFunction)

  object functionsSupporter extends PreambleEmitter {
    private var collectedFunctions = Set[ast.ProgramFunction]()
    private var translatedFunctions = Set[Function]()
    private var funcToLocToSnap = Map[ast.ProgramFunction, Map[ast.LocationAccess, Term]]()
    private var axiomGenerators = Set[() => Set[Term]]()
//    private var axioms = Set[Term]()

    def verifyFunctionAndPrepareAxiomatization(function: ast.ProgramFunction, c: C): VerificationResult = {
      logger.debug("\n\n" + "-" * 10 + " FUNCTION " + function.name + "-" * 10 + "\n")
      decider.prover.logComment("%s %s %s".format("-" * 10, function.name, "-" * 10))

//      println(s"\n[axiomatizeFunction] ${function.name}")

      val ins = function.formalArgs.map(_.localVar)
      val out = function.result

      val γ = Γ((out, fresh(out)) +: ins.map(v => (v, fresh(v))))
      val σ = Σ(γ, Ø, Ø)

      val postError = (offendingNode: ast.Expression) => PostconditionViolated(offendingNode, function)
      val malformedError = (_: ast.Expression) => FunctionNotWellformed(function)
      val internalError = (offendingNode: ast.Expression) => Internal(offendingNode)

      /* Produce includes well-formedness check */
      inScope {
        (inScope {
          produces(σ, fresh, FullPerm(), function.pres ++ function.posts, malformedError, c)((_, c2) =>
            Success())}
            &&
            inScope {
//              println(s"\n--------- ---- ${function.name} ----- ---------")
              val c1 = c // c.copy(recordAccesses = true)
              val pres = ast.utils.BigAnd(function.pres)
              produce(σ, fresh, FullPerm(), pres, Internal(pres), c1)((σ1, c2) => {
//              produces(σ, fresh, FullPerm(), function.pres, internalError, c1)((σ1, c2) =>
                eval(σ1, function.exp, FunctionNotWellformed(function), c2)((tB, c3) => {
//                  println(s"\n  --- ${function.name} ---\n")
                  val c4 = c3 // c3.copy(recordAccesses = false)
//                  println(s"  chunkToSnap = ${c4.chunkToSnap}")
//                  println(s"  locToChunk = ${c4.locToChunk}")
//                  println(s"  " + decider.π)
                  //                  val locToSnap = c4.locToSnap // cc4.locToChunk.map{case (loc, ch) => loc -> c4.chunkToSnap(ch)}
//                  println("  locToSnap =")
//                  c4.locToSnap foreach {case (loc, snap) => println(s"    $loc -> $snap") }

                  funcToLocToSnap += function -> (funcToLocToSnap.get(function) match {
                    case None => c4.locToSnap
                    case Some(locToSnap) =>
                      silicon.utils.conflictFreeUnion(locToSnap, c4.locToSnap) match {
                        case Right(lts) => lts
                        case _ => sys.error("Unexpected situation while axiomatising functions")
                      }
                  })

//                  println()
//                  funcToLocToSnap(function) foreach println

//                  c4.locToChunk.foreach{case (loc, ch) =>
//                    println(s"  $loc -> ${c4.chunkToSnap(ch)}")
//                  }
//                  val termToSnap = c4.locToChunk.map{case (loc, ch) =>
//                    val t =  ch match {
//                      case fch: FieldChunk => fch.value
//                      case pch: PredicateChunk => pch.snap
//                    }
//
//                    t -> c4.chunkToSnap(ch)
//                  }
//                  //                  println(s"  tB = $tB")
//                  val fb = tB.replace(termToSnap)
//                  println(s"  fb = $fb")
                  consumes(σ1 \+ (out, tB), FullPerm(), function.posts, postError, c4)((_, _, _, _) =>
                    Success())})})})}
    }

//    private def disjointUnion[K, V](m1: Map[K, V], m2: Map[K,V], errmsg: String) = {
//      assert(m1.keys.toSet.intersect(m2.keys.toSet).isEmpty, errmsg)
//
//      m1 ++ m2
//    }

    def analyze(program: ast.Program) {
      program visit {
        case func: ast.ProgramFunction => collectedFunctions += func
        case _ => /* Ignore */
      }

      generateFunctionSymbols(program)
    }

    private def generateFunctionSymbols(program: ast.Program) {
      collectedFunctions foreach { silverFunc =>
        val func = symbolConverter.toFunction(silverFunc)
        translatedFunctions += func

        val vs = silverFunc.formalArgs map (v => Var(v.name, symbolConverter.toSort(v.typ)))
        val fapp = FApp(func, `?s`, vs)
        val trs = Seq(Trigger(Seq(fapp)))

        val limFunc = limitedFunction(func)
        translatedFunctions += limFunc

        /* The axioms can only be generated after the functions have been verified
         * because the relations between accessibility predicates occurring in the
         * precondition and location accesses occurring in the function body (and
         * pre/post) are recorded while the function is verified.
         */

        axiomGenerators += (() => {
          val limFApp = FApp(limFunc, `?s`, vs)
          val limEq = limFApp === fapp
          val limAx = Quantification(Forall, Seq(`?s`) ++ vs, limEq, trs)
//          axioms += limAx

//          println(fapp.function.id)
          val locToSnap = funcToLocToSnap.getOrElse(silverFunc, Map())
            /* If silverFunc isn't well-formed then the entry might be missing*/

          val body = expressionTranslator.translate(program, silverFunc, locToSnap)
          val nonNulls = True()
          //        val nonNulls = utils.BigAnd(
          //          map.collect{case (fa: ast.FieldAccess, _) => fa.rcv}
          //              .map(rcv => expressionTranslator.translate(rcv, map) !== terms.Null())
          //              .toSet[Term])
          val eq = fapp === body
          val ax = Quantification(Forall, Seq(`?s`) ++ vs, And(nonNulls, eq), trs)
//          axioms += ax

          Set(ax, limAx)
        })
      }
    }

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

    def limitedFunction(funcSymbol: Function) =
      Function(funcSymbol.id + "$", funcSymbol.sort)

    val sorts = Set[Sort]()

    def declareSorts() {}

    def symbols = Some(translatedFunctions)

    def declareSymbols() {
      translatedFunctions foreach (func => decider.prover.declare(FunctionDecl(func)))
    }

    def emitAxioms() {
//      axioms foreach decider.prover.assume
      axiomGenerators foreach (_() foreach decider.prover.assume)
    }

    /* Lifetime */

    def start() {}

    def reset() {
      collectedFunctions = collectedFunctions.empty
      translatedFunctions = translatedFunctions.empty
      funcToLocToSnap = funcToLocToSnap.empty
      axiomGenerators = axiomGenerators.empty
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
  private var parentFunc: ast.ProgramFunction = null

  def translate(program: ast.Program, func: ast.ProgramFunction, locToSnap: Map[ast.LocationAccess, Term]): Term = {
    val oldProgram = this.program
    val oldParentFunc = parentFunc

    this.program = program
    this.parentFunc = func
    val body = translate(program, func.exp, locToSnap)

    this.program = oldProgram
    this.parentFunc = oldParentFunc

    body
  }

  def translate(program: ast.Program, exp: ast.Expression, locToSnap: Map[ast.LocationAccess, Term]): Term = {
    val oldProgram = this.program
    val oldLocToSnap = this.locToSnap

    this.program = program
    this.locToSnap = locToSnap
    val t = translate(toSort)(exp)

    this.program = oldProgram
    this.locToSnap = oldLocToSnap

    t
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
        val sort = toSort(loc.typ, Map())

        val snap = locToSnap.get(loc) match {
          case None =>
            /* It is assumed that the entry is missing because the currently
             * translated function is malformed. In order to be able to continue
             * we use a fresh term (instead of aborting)
             */
            fresh("$unresolvedLocAcc", sort)

          case Some(s) =>
            s.convert(sort)
        }

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
        val args = eFApp.args map (arg => translate(program, arg, locToSnap))
        val fapp = FApp(func, null, args)
//        val tFApp = translateFuncApp(eFApp, snap, accs)

        if (eFApp.func == parentFunc)
          fapp.copy(function = limitedFunction(fapp.function))
        else
          fapp

      case _ =>
        super.translate(toSort)(e)
    }
}
