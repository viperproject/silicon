/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.functions

import com.typesafe.scalalogging.LazyLogging
import viper.silver.ast
import viper.silicon.Map
import viper.silicon.rules.functionSupporter
import viper.silicon.state.{Identifier, SimpleIdentifier, SuffixedIdentifier, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.supporters.ExpressionTranslator

class HeapAccessReplacingExpressionTranslator(symbolConverter: SymbolConverter,
                                              fresh: (String, Sort) => Var)
    extends ExpressionTranslator
       with LazyLogging {

  private var program: ast.Program = _
  private var func: ast.Function = _
  private var data: FunctionData = _
  private var ignoreAccessPredicates = false
  private var failed = false

  var functionData: Map[ast.Function, FunctionData] = _

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
    translate(symbolConverter.toSort _)(exp)
  }

  def translatePostcondition(program: ast.Program,
                             posts: Seq[ast.Exp],
                             data: FunctionData)
                            : Seq[Term] = {

    this.program = program
    this.data = data
    this.failed = false

    posts.map(p => translate(symbolConverter.toSort _)(p.whenInhaling))
  }

  def translatePrecondition(program: ast.Program,
                            pres: Seq[ast.Exp],
                            data: FunctionData)
                           : Seq[Term] = {

    this.program = program
    this.data = data
    this.ignoreAccessPredicates = true
    this.failed = false

    pres.map(p => translate(symbolConverter.toSort _)(p.whenExhaling))
  }

  /* Attention: Expects some fields, e.g., `program` and `locToSnap`, to be
   * set, depending on which kind of translation is performed.
   * See public `translate` methods.
   */
  override protected def translate(toSort: ast.Type => Sort)
                                  (e: ast.Exp)
                                  : Term =

    e match {
      case _: ast.AccessPredicate | _: ast.MagicWand if ignoreAccessPredicates => True()
      case q: ast.Forall if !q.isPure && ignoreAccessPredicates => True()

      case _: ast.Result => data.formalResult

      case v: ast.AbstractLocalVar =>
        data.formalArgs.get(v) match {
          case Some(t) => t
          case None => Var(Identifier(v.name), toSort(v.typ))
        }

      case eQuant: ast.QuantifiedExp =>
        /* Local variables that are not parameters of the function itself, i.e. quantified
         * and let-bound variables, are translated as-is, e.g. 'x' will be translated to 'x',
         * not to some 'x@i'. If a local variable occurs in a term that was recorded during
         * the well-definedness checking & verification of a function, e.g. a mapping such as
         * 'e.f |-> lookup(...)' from field access to snapshot, the recorded term potentially
         * contains occurrences of such local variables. However, recorded terms contain
         * occurrences where the local variables *are* suffixed, i.e. of the form 'x@i'.
         * Hence, the body of a quantifier is processed after being translated, and each
         * occurrence of 'x@i' is replaced by 'x', for all variables 'x@i' where the prefix
         * 'x' is bound by the surrounding quantifier.
         */
        val tQuant = super.translate(symbolConverter.toSort)(eQuant).asInstanceOf[Quantification]
        val names = tQuant.vars.map(_.id.name)

        tQuant.transform({ case v: Var =>
          v.id match {
            case sid: SuffixedIdentifier if names.contains(sid.prefix) => Var(SimpleIdentifier(sid.prefix), v.sort)
            case _ => v
          }
        })()

      case loc: ast.LocationAccess => getOrFail(data.locToSnap, loc, toSort(loc.typ), data.programFunction.name)
      case ast.Unfolding(_, eIn) => translate(toSort)(eIn)
      case ast.Applying(_, eIn) => translate(toSort)(eIn)

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
          fapp.copy(applicable = functionSupporter.limitedVersion(fun))

      case _ => super.translate(symbolConverter.toSort)(e)
    }

  def getOrFail[K <: ast.Positioned](map: Map[K, Term], key: K, sort: Sort, fname: String): Term =
    map.get(key) match {
      case Some(s) =>
        s.convert(sort)
      case None =>
        if (!failed && data.verificationFailures.isEmpty)
          logger.warn(s"Could not resolve $key (${key.pos}) during the axiomatisation of function $fname")

        failed = true

        fresh("$unresolved", sort)
    }
}
