package viper
package silicon
package theories

import state.{terms, SymbolConvert}
import state.terms.Term

trait ExpressionTranslator {
  val symbolConverter: SymbolConvert

  /**
   *
   * @param toSort
   * @param exp
   * @return
    *
   * TODO: Shares a lot of code with DefaultEvaluator. Unfortunately, it doesn't seem to be easy to
   *       reuse code because the code in DefaultEvaluator uses the state whereas this one here
   *       doesn't. Of course, one could just evaluate the domains using the DefaultEvaluator - which
   *       was done before - but that is less efficient and creates lots of additional noise output
   *       in the prover log.
   *
   * TODO: Can't we do without toSort? Or at least with a less type-specific one?
   */
  protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => terms.Sort)
                         (exp: ast.Expression)
                         : Term = {

    val f = translate(toSort) _

    exp match {
      /* TODO: Translate triggers */
      case q @ ast.Quantified(qvars, body) =>
        val (quantifier, triggers) = q match {
          case fa: ast.Forall => (terms.Forall, fa.autoTrigger.triggers)
          case _: ast.Exists => (terms.Exists, Nil)
        }
        terms.Quantification(quantifier,
                             qvars map (v => terms.Var(v.name, toSort(v.typ, Map()))),
                             f(body),
                             triggers map (tr => terms.Trigger(tr.exps map f)))

      case ast.True() => terms.True()
      case ast.False() => terms.False()
      case ast.Not(e0) => terms.Not(f(e0))
      case ast.And(e0, e1) => terms.And(f(e0), f(e1))
      case ast.Or(e0, e1) => terms.Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => terms.Implies(f(e0), f(e1))
      case ast.Ite(e0, e1, e2) => terms.Ite(f(e0), f(e1), f(e2))

      case ast.Equals(e0, e1) => terms.Eq(f(e0), f(e1))
      case ast.Unequals(e0, e1) => terms.Not(terms.Eq(f(e0), f(e1)))

      case ast.IntegerLiteral(n) => terms.IntLiteral(n)
      case ast.IntPlus(e0, e1) => terms.Plus(f(e0), f(e1))
      case ast.IntMinus(e0, e1) => terms.Minus(f(e0), f(e1))
      case ast.IntTimes(e0, e1) => terms.Times(f(e0), f(e1))
      case ast.IntDiv(e0, e1) => terms.Div(f(e0), f(e1))
      case ast.IntMod(e0, e1) => terms.Mod(f(e0), f(e1))
      case ast.IntNeg(e0) => terms.Minus(terms.IntLiteral(0), f(e0))

      case ast.IntGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.IntGT(e0, e1) => terms.Greater(f(e0), f(e1))
      case ast.IntLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.IntLT(e0, e1) => terms.Less(f(e0), f(e1))

      case ast.NullLiteral() => terms.Null()

      case v: ast.Variable => terms.Var(v.name, toSort(v.typ, Map()))

      case ast.DomainFuncApp(funcName, args, typeVarMap) =>
        val tArgs = args map f
        val inSorts = tArgs map (_.sort)
        val outSort = toSort(exp.typ, toMap(typeVarMap))
        val id = symbolConverter.toSortSpecificId(funcName, inSorts :+ outSort)
        val df = terms.Function(id, inSorts, outSort)
        terms.DomainFApp(df, tArgs)

      case _: ast.FullPerm => terms.FullPerm()
      case _: ast.NoPerm => terms.NoPerm()
      case ast.FractionalPerm(e0, e1) => terms.FractionPerm(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))

      case ast.PermPlus(e0, e1) => terms.PermPlus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermMinus(e0, e1) => terms.PermMinus(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.PermTimes(e0, e1) => terms.PermTimes(terms.TermPerm(f(e0)), terms.TermPerm(f(e1)))
      case ast.IntPermTimes(e0, e1) => terms.IntPermTimes(f(e0), terms.TermPerm(f(e1)))
      case ast.PermLE(e0, e1) => terms.AtMost(f(e0), f(e1))
      case ast.PermLT(e0, e1) => terms.Less(f(e0), f(e1))
      case ast.PermGE(e0, e1) => terms.AtLeast(f(e0), f(e1))
      case ast.PermGT(e0, e1) => terms.Greater(f(e0), f(e1))

      case silver.ast.SeqAppend(e0, e1) => terms.SeqAppend(f(e0), f(e1))
      case silver.ast.SeqContains(e0, e1) => terms.SeqIn(f(e1), f(e0))
      case silver.ast.SeqDrop(e0, e1) => terms.SeqDrop(f(e0), f(e1))
      case silver.ast.SeqIndex(e0, e1) => terms.SeqAt(f(e0), f(e1))
      case silver.ast.SeqLength(e) => terms.SeqLength(f(e))
      case silver.ast.SeqTake(e0, e1) => terms.SeqTake(f(e0), f(e1))
      case silver.ast.EmptySeq(typ) => terms.SeqNil(toSort(typ, Map()))
      case silver.ast.RangeSeq(e0, e1) => terms.SeqRanged(f(e0), f(e1))
      case silver.ast.SeqUpdate(e0, e1, e2) => terms.SeqUpdate(f(e0), f(e1), f(e2))

      case silver.ast.ExplicitSeq(es) =>
        es.tail.foldLeft[terms.SeqTerm](terms.SeqSingleton(f(es.head)))((tSeq, e) =>
          terms.SeqAppend(terms.SeqSingleton(f(e)), tSeq))

      case _: silver.ast.MultisetExp | _: silver.ast.EmptySet | _: silver.ast.ExplicitSet =>
        sys.error(s"Found unexpected expression $exp (${exp.getClass.getName}})")

      case   _: ast.LocationAccess | _: ast.AccessPredicate | _: ast.Old | _: ast.FractionalPerm
             | _: ast.ResultLiteral | _: ast.Unfolding | _: ast.InhaleExhale | _: ast.PredicateAccess
             | _: ast.FuncApp | _: ast.CurrentPerm | _: ast.EpsilonPerm  | _: ast.WildcardPerm | _: ast.EpsilonPerm =>

        sys.error(s"Found unexpected expression $exp (${exp.getClass.getName}})")
    }
  }
}
