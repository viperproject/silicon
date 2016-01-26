/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import org.slf4s.Logging
import viper.silver.ast
import viper.silicon.{Map, Set}
import viper.silicon.state.SymbolConvert
import viper.silicon.state.terms._
import viper.silicon.supporters.ExpressionTranslator

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
                             posts: Seq[ast.Exp],
                             data: FunctionData)
                            : Seq[Term] = {

    this.program = program
    this.data = data
    this.failed = false

    posts map translate(toSort)
  }

  def translatePrecondition(program: ast.Program,
                            pres: Seq[ast.Exp],
                            data: FunctionData)
                           : Seq[Term] = {

    this.program = program
    this.data = data
    this.ignoreAccessPredicates = true
    this.failed = false

    pres map translate(toSort)
  }

  /* Attention: Expects some fields, e.g., `program` and `locToSnap`, to be
   * set, depending on which kind of translation is performed.
   * See public `translate` methods.
   */
  override protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort,
                                   qpFields: Set[ast.Field] = data.quantifiedFields)
                                  (e: ast.Exp)
                                  : Term =

    e match {
      case _: ast.Result => data.limitedFunctionApplication

      case v: ast.AbstractLocalVar =>
        data.formalArgs.get(v) match {
          case Some(t) => t
          case None => super.translate(toSort, qpFields)(v)
        }

      case loc: ast.LocationAccess => getOrFail(data.locToSnap, loc, toSort(loc.typ, Map()), data.programFunction.name)
      case ast.Unfolding(_, eIn) => translate(toSort)(eIn)

      case eFApp: ast.FuncApp =>
        val silverFunc = program.findFunction(eFApp.funcname)
        val fun = symbolConverter.toFunction(silverFunc)
        val args = eFApp.args map (arg => translate(arg))
        val snap = getOrFail(data.fappToSnap, eFApp, sorts.Snap, data.programFunction.name)
        val fapp = App(fun, snap +: args)

        val callerHeight = data.height
        val calleeHeight = functionData(eFApp.func(program)).height

        if (callerHeight < calleeHeight)
          fapp
        else
          fapp.copy(applicable = FunctionSupporter.limitedVersion(fun))

      case _: ast.AccessPredicate if ignoreAccessPredicates => True()
      case q: ast.Forall if !q.isPure && ignoreAccessPredicates => True()
      case _ => super.translate(toSort, qpFields)(e)
    }

  def getOrFail[K <: ast.Positioned](map: Map[K, Term], key: K, sort: Sort, fname: String): Term =
    map.get(key) match {
      case Some(s) =>
        s.convert(sort)
      case None =>
        if (!failed && data.verificationFailures.isEmpty)
          log.warn(s"Could not resolve $key (${key.pos}) during the axiomatisation of function $fname")

        failed = true

        fresh("$unresolved", sort)
    }
}
