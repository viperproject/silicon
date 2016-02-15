/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.{Map, Set, toMap}
import viper.silicon.state.{Identifier, SymbolConvert}
import viper.silicon.state.terms._
import viper.silicon.supporters.functions.FunctionSupporter

trait ExpressionTranslator {
  val symbolConverter: SymbolConvert

  /* TODO: Shares a lot of code with DefaultEvaluator. Unfortunately, it doesn't seem to be easy to
   *       reuse code because the code in DefaultEvaluator uses the state whereas this one here
   *       doesn't. Of course, one could just evaluate the domains using the DefaultEvaluator - which
   *       was done before - but that is less efficient and creates lots of additional noise output
   *       in the prover log.
   *
   * TODO: Can't we do without toSort? Or at least with a less type-specific one?
   */
  protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort,
                          qpFields: Set[ast.Field])
                         (exp: ast.Exp)
                         : Term = {

    val f = translate(toSort, qpFields) _

    def translateAnySetUnExp(exp: ast.AnySetUnExp,
                             setTerm: Term => Term,
                             multisetTerm: Term => Term,
                             anysetTypedExp: ast.Exp = exp) =

      anysetTypedExp.typ match {
        case _: ast.SetType => setTerm(f(exp.exp))
        case _: ast.MultisetType => multisetTerm(f(exp.exp))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(exp, exp.getClass.getName, exp.typ))
      }

    def translateAnySetBinExp(exp: ast.AnySetBinExp,
                              setTerm: (Term, Term) => Term,
                              multisetTerm: (Term, Term) => Term,
                              anysetTypedExp: ast.Exp = exp) =

      anysetTypedExp.typ match {
        case _: ast.SetType => setTerm(f(exp.left), f(exp.right))
        case _: ast.MultisetType => multisetTerm(f(exp.left), f(exp.right))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(anysetTypedExp, anysetTypedExp.getClass.getName, anysetTypedExp.typ))
      }


    exp match {
      case sourceQuant: ast.QuantifiedExp =>
        /* IMPORTANT: Keep in sync with [[DefaultEvaluator.eval]]
         *
         * TODO: Avoid this code duplication.
         *
         * TODO: In the long run, it might be better to not
         *         1. record data while verifying a function
         *         2. and to then translate the function using the recorded data
         *       but to instead create the function definition axioms from the
         *       terms that the evaluation of the function body (and the
         *       postcondition) yielded.
         */

        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            val autoTriggeredForall = viper.silicon.utils.ast.autoTrigger(forall, qpFields)
            (autoTriggeredForall, Forall, autoTriggeredForall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, Seq())
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }

        val body = eQuant.exp
        val vars = eQuant.variables map (_.localVar)

        /** IMPORTANT: Keep in sync with [[viper.silicon.DefaultEvaluator.evalTrigger]] */
        val translatedTriggers = eTriggers map (triggerSet => Trigger(triggerSet.exps map (trigger =>
          f(trigger) match {
            case app @ App(fun: HeapDepFun, _) =>
              app.copy(applicable = FunctionSupporter.limitedVersion(fun))
            case other => other
          }
        )))

        Quantification(qantOp,
                       vars map (v => Var(Identifier(v.name), toSort(v.typ, Map()))),
                       f(body),
                       translatedTriggers)

      case _: ast.TrueLit => True()
      case _: ast.FalseLit => False()
      case ast.Not(e0) => Not(f(e0))
      case ast.And(e0, e1) => And(f(e0), f(e1))
      case ast.Or(e0, e1) => Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => Implies(f(e0), f(e1))
      case ast.CondExp(e0, e1, e2) => Ite(f(e0), f(e1), f(e2))

      case ast.EqCmp(e0, e1) => Equals(f(e0), f(e1))
      case ast.NeCmp(e0, e1) => Not(Equals(f(e0), f(e1)))

      case ast.IntLit(n) => IntLiteral(n)
      case ast.Add(e0, e1) => Plus(f(e0), f(e1))
      case ast.Sub(e0, e1) => Minus(f(e0), f(e1))
      case ast.Mul(e0, e1) => Times(f(e0), f(e1))
      case ast.Div(e0, e1) => Div(f(e0), f(e1))
      case ast.Mod(e0, e1) => Mod(f(e0), f(e1))
      case ast.Minus(e0) => Minus(IntLiteral(0), f(e0))

      case ast.GeCmp(e0, e1) => AtLeast(f(e0), f(e1))
      case ast.GtCmp(e0, e1) => Greater(f(e0), f(e1))
      case ast.LeCmp(e0, e1) => AtMost(f(e0), f(e1))
      case ast.LtCmp(e0, e1) => Less(f(e0), f(e1))

      case _: ast.NullLit => Null()

      case v: ast.AbstractLocalVar => Var(Identifier(v.name), toSort(v.typ, Map()))

      case ast.DomainFuncApp(funcName, args, typeVarMap) =>
        val tArgs = args map f
        val inSorts = tArgs map (_.sort)
        val outSort = toSort(exp.typ, toMap(typeVarMap))
        val id = symbolConverter.toSortSpecificId(funcName, inSorts :+ outSort)
        val df = Fun(id, inSorts, outSort)
        App(df, tArgs)

      /* Permissions */

      case _: ast.FullPerm => FullPerm()
      case _: ast.NoPerm => NoPerm()
      case ast.FractionalPerm(e0, e1) => FractionPerm(f(e0), f(e1))

      case ast.PermAdd(e0, e1) => PermPlus(f(e0), f(e1))
      case ast.PermSub(e0, e1) => PermMinus(f(e0), f(e1))
      case ast.PermMul(e0, e1) => PermTimes(f(e0), f(e1))
      case ast.IntPermMul(e0, e1) => IntPermTimes(f(e0), f(e1))
      case ast.PermDiv(e0, e1) => PermIntDiv(f(e0), f(e1))
      case ast.PermLeCmp(e0, e1) => AtMost(f(e0), f(e1))
      case ast.PermLtCmp(e0, e1) => Less(f(e0), f(e1))
      case ast.PermGeCmp(e0, e1) => AtLeast(f(e0), f(e1))
      case ast.PermGtCmp(e0, e1) => Greater(f(e0), f(e1))

      /* Sequences */

      case ast.SeqAppend(e0, e1) => SeqAppend(f(e0), f(e1))
      case ast.SeqContains(e0, e1) => SeqIn(f(e1), f(e0))
      case ast.SeqDrop(e0, e1) => SeqDrop(f(e0), f(e1))
      case ast.SeqIndex(e0, e1) => SeqAt(f(e0), f(e1))
      case ast.SeqLength(e) => SeqLength(f(e))
      case ast.SeqTake(e0, e1) => SeqTake(f(e0), f(e1))
      case ast.EmptySeq(typ) => SeqNil(toSort(typ, Map()))
      case ast.RangeSeq(e0, e1) => SeqRanged(f(e0), f(e1))
      case ast.SeqUpdate(e0, e1, e2) => SeqUpdate(f(e0), f(e1), f(e2))

      case ast.ExplicitSeq(es) =>
        es.tail.foldLeft[SeqTerm](SeqSingleton(f(es.head)))((tSeq, e) =>
          SeqAppend(tSeq, SeqSingleton(f(e))))

      /* Sets and multisets */

      case ast.EmptySet(typ) => EmptySet(toSort(typ, Map()))
      case ast.EmptyMultiset(typ) => EmptyMultiset(toSort(typ, Map()))

      case ast.ExplicitSet(es) =>
        es.tail.foldLeft[SetTerm](SingletonSet(f(es.head)))((tSet, e) =>
          SetAdd(tSet, f(e)))

      case ast.ExplicitMultiset(es) =>
        es.tail.foldLeft[MultisetTerm](SingletonMultiset(f(es.head)))((tMultiset, e) =>
          MultisetAdd(tMultiset, f(e)))

      case as: ast.AnySetUnion => translateAnySetBinExp(as, SetUnion, MultisetUnion)
      case as: ast.AnySetIntersection => translateAnySetBinExp(as, SetIntersection, MultisetIntersection)
      case as: ast.AnySetSubset => translateAnySetBinExp(as, SetSubset, MultisetSubset)
      case as: ast.AnySetMinus => translateAnySetBinExp(as, SetDifference, MultisetDifference)
      case as: ast.AnySetContains => translateAnySetBinExp(as, SetIn, (t0, t1) => MultisetCount(t1, t0), as.right)
      case as: ast.AnySetCardinality => translateAnySetUnExp(as, SetCardinality, MultisetCardinality, as.exp)

      /* Other expressions */

      case ast.Let(lvd, e, body) => Let(f(lvd.localVar).asInstanceOf[Var], f(e), f(body))

      /* Unsupported (because unexpected) expressions */

      case     _: ast.LocationAccess
             | _: ast.AccessPredicate
             | _: ast.Old
             | _: ast.LabelledOld
             | _: ast.FractionalPerm
             | _: ast.Result
             | _: ast.Unfolding
             | _: ast.InhaleExhaleExp
             | _: ast.PredicateAccess
             | _: ast.FuncApp
             | _: ast.CurrentPerm
             | _: ast.EpsilonPerm
             | _: ast.WildcardPerm
             | _: ast.EpsilonPerm
             | _: ast.ForPerm
             | _: ast.ApplyOld
             | _: ast.Applying
             | _: ast.Folding
             | _: ast.MagicWand
             | _: ast.Packaging
             =>

        sys.error(s"Found unexpected expression $exp (${exp.getClass.getName}})")
    }
  }
}
