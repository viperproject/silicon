// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.silicon.supporters.functions

import com.typesafe.scalalogging.LazyLogging

import scala.annotation.unused
import viper.silver.ast
import viper.silicon.Map
import viper.silicon.rules.{functionSupporter, maskHeapSupporter}
import viper.silicon.state.{Identifier, SimpleIdentifier, SuffixedIdentifier, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.supporters.ExpressionTranslator
import viper.silicon.utils.ast.extractPTypeFromExp
import viper.silicon.verifier.Verifier
import viper.silver.parser.{PType, PUnknown}
import viper.silver.ast.AnnotationInfo
import viper.silver.reporter.{InternalWarningMessage, Reporter}

class HeapAccessReplacingExpressionTranslator(symbolConverter: SymbolConverter,
                                              fresh: (String, Sort, Option[PType]) => Var,
                                              resolutionFailureMessage: (ast.Positioned, FunctionData) => String,
                                              stopOnResolutionFailure: (ast.Positioned, FunctionData) => Boolean,
                                              reporter: Reporter)
    extends ExpressionTranslator
       with LazyLogging {

  protected var program: ast.Program = _
  @unused private var func: ast.Function = _
  private var data: FunctionData = _
  private var ignoreAccessPredicates = false
  private var failed = false
  private var context: Seq[ExpContext] = Seq.empty

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
      case _: ast.AccessPredicate | _: ast.MagicWand if ignoreAccessPredicates => True
      case q: ast.Forall if !q.isPure && ignoreAccessPredicates => True

      case _: ast.Result => data.formalResult
      case l@ast.Let(lvd, e, body) =>
        val bvar = translate(toSort)(lvd.localVar)
        val tE = translate(toSort)(e)
        context = context :+ LetContext(l)
        val tBody = translate(toSort)(body)
        context = context.init
        Let(bvar.asInstanceOf[Var], tE, tBody)

      case v: ast.AbstractLocalVar =>
        data.formalArgs.get(v) match {
          case Some(t) => t
          case None => Var(Identifier(v.name), toSort(v.typ), false)
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
        context = context :+ QuantifierContext(eQuant)
        val tQuant = super.translate(symbolConverter.toSort)(eQuant).asInstanceOf[Quantification]
        val names = tQuant.vars.map(_.id.name)

        val res = tQuant.transform({ case v: Var =>
          v.id match {
            case sid: SuffixedIdentifier if names.contains(sid.prefix.name) =>
              Var(SimpleIdentifier(sid.prefix.name), v.sort, false)
            case _ => v
          }
        })()
        context = context.init
        res

      case loc: ast.LocationAccess => getOrFail(data.locToSnap, loc, context, toSort(loc.typ), Option.when(Verifier.config.enableDebugging())(extractPTypeFromExp(loc)))
      case ast.Unfolding(_, eIn) => translate(toSort)(eIn)
      case ast.Applying(_, eIn) => translate(toSort)(eIn)
      case ast.Asserting(_, eIn) => translate(toSort)(eIn)

      case eFApp: ast.FuncApp =>
        val silverFunc = program.findFunction(eFApp.funcname)
        val funcAnn = silverFunc.info.getUniqueInfo[AnnotationInfo]
        val callerHeight = data.height
        val calleeHeight = functionData(eFApp.func(program)).height
        val funDefined = symbolConverter.toFunction(silverFunc, program)
        val funDefault = if (callerHeight < calleeHeight)
          funDefined
        else
          functionSupporter.limitedVersion(funDefined)
        val fun = funcAnn match {
          case Some(a) if a.values.contains("opaque") =>
            val funcAppAnn = eFApp.info.getUniqueInfo[AnnotationInfo]
            funcAppAnn match {
              case Some(a) if a.values.contains("reveal") => funDefault
              case _ => functionSupporter.limitedVersion(symbolConverter.toFunction(silverFunc, program))
            }
          case _ => funDefault
        }
        val args = eFApp.args map (arg => translate(arg))
        val snap = getOrFail(data.fappToSnap, eFApp, context, sorts.Snap, Option.when(Verifier.config.enableDebugging())(PUnknown()))
        val fapp = if (Verifier.config.maskHeapMode()) {
          def createApp(trm: Term): Term = trm match {
            case mt: FakeMaskMapTerm => App(fun, mt.masks.values.toSeq ++ args)
            case Ite(cond, e1, e2) => Ite(cond, createApp(e1), createApp(e2))
            case v: Var =>
              val resources = maskHeapSupporter.getResourceSeq(silverFunc.pres, program)
              val resHeaps = fromSnapTree(v, resources.size).zip(resources).map {
                case (s, r) =>
                  val srt = r match {
                    case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
                    case _ => sorts.PredHeapSort
                  }
                  SnapToHeap(s, r, srt)
              }
              App(fun, resHeaps ++ args)
          }

          createApp(snap)
        } else {
          App(fun, snap +: args)
        }
        fapp

      case _ => super.translate(symbolConverter.toSort)(e)
    }

  def getOrFail[K <: ast.Positioned](map: Map[(K, Seq[ExpContext]), Term], key: K, ctx: Seq[ExpContext], sort: Sort, pType: Option[PType]): Term =
    map.get((key, ctx)) match {
      case Some(s) =>
        s.convert(sort)
      case None =>
        if (!failed && data.verificationFailures.isEmpty) {
          val msg = resolutionFailureMessage(key, data)

          reporter report InternalWarningMessage(msg)
          logger warn msg
        }

        failed = failed || stopOnResolutionFailure(key, data)

        /* TODO: Fresh symbol $unresolved must be a function of all currently quantified variables,
         *       including the formal arguments of a function, if the unresolved expression is from
         *       a function body.
         */
        fresh("$unresolved", sort, pType)
    }
}
