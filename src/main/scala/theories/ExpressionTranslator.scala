package viper
package silicon
package theories

import state.SymbolConvert
import state.terms._

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
  protected def translate(toSort: (ast.Type, Map[ast.TypeVar, ast.Type]) => Sort)
                         (exp: ast.Expression)
                         : Term = {

    val f = translate(toSort) _

    def translateAnySetUnExp(exp: silver.ast.AnySetUnExp,
                             setTerm: Term => Term,
                             multisetTerm: Term => Term) =

      exp.typ match {
        case _: ast.types.Set => setTerm(f(exp.exp))
        case _: ast.types.Multiset => multisetTerm(f(exp.exp))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(exp, exp.getClass.getName, exp.typ))
      }

    def translateAnySetBinExp(exp: silver.ast.AnySetBinExp,
                              setTerm: (Term, Term) => Term,
                              multisetTerm: (Term, Term) => Term,
                              anysetTypedExp: ast.Expression = exp) =

      anysetTypedExp.typ match {
        case _: ast.types.Set => setTerm(f(exp.left), f(exp.right))
        case _: ast.types.Multiset => multisetTerm(f(exp.left), f(exp.right))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(anysetTypedExp, anysetTypedExp.getClass.getName, anysetTypedExp.typ))
      }


    exp match {
      case q @ ast.Quantified(qvars, _) =>
        val (autoTriggerQuant, quantifier, triggers) = q match {
          case fa: ast.Forall => (fa.autoTrigger, Forall, fa.autoTrigger.triggers)
          case ex: ast.Exists => (ex, Exists, Seq())
        }

        Quantification(quantifier,
                       qvars map (v => Var(v.name, toSort(v.typ, Map()))),
                       f(autoTriggerQuant.exp),
                       triggers map (tr => Trigger(tr.exps map f)))

      case ast.True() => True()
      case ast.False() => False()
      case ast.Not(e0) => Not(f(e0))
      case ast.And(e0, e1) => And(f(e0), f(e1))
      case ast.Or(e0, e1) => Or(f(e0), f(e1))
      case ast.Implies(e0, e1) => Implies(f(e0), f(e1))
      case ast.Ite(e0, e1, e2) => Ite(f(e0), f(e1), f(e2))

      case ast.Equals(e0, e1) => Equals(f(e0), f(e1))
      case ast.Unequals(e0, e1) => Not(Equals(f(e0), f(e1)))

      case ast.IntegerLiteral(n) => IntLiteral(n)
      case ast.IntPlus(e0, e1) => Plus(f(e0), f(e1))
      case ast.IntMinus(e0, e1) => Minus(f(e0), f(e1))
      case ast.IntTimes(e0, e1) => Times(f(e0), f(e1))
      case ast.IntDiv(e0, e1) => Div(f(e0), f(e1))
      case ast.IntMod(e0, e1) => Mod(f(e0), f(e1))
      case ast.IntNeg(e0) => Minus(IntLiteral(0), f(e0))

      case ast.IntGE(e0, e1) => AtLeast(f(e0), f(e1))
      case ast.IntGT(e0, e1) => Greater(f(e0), f(e1))
      case ast.IntLE(e0, e1) => AtMost(f(e0), f(e1))
      case ast.IntLT(e0, e1) => Less(f(e0), f(e1))

      case ast.NullLiteral() => Null()

      case v: ast.Variable => Var(v.name, toSort(v.typ, Map()))

      case ast.DomainFuncApp(funcName, args, typeVarMap) =>
        val tArgs = args map f
        val inSorts = tArgs map (_.sort)
        val outSort = toSort(exp.typ, toMap(typeVarMap))
        val id = symbolConverter.toSortSpecificId(funcName, inSorts :+ outSort)
        val df = Function(id, inSorts, outSort)
        DomainFApp(df, tArgs)

      /* Permissions */

      case _: ast.FullPerm => FullPerm()
      case _: ast.NoPerm => NoPerm()
      case ast.FractionalPerm(e0, e1) => FractionPerm(f(e0), f(e1))

      case ast.PermPlus(e0, e1) => PermPlus(f(e0), f(e1))
      case ast.PermMinus(e0, e1) => PermMinus(f(e0), f(e1))
      case ast.PermTimes(e0, e1) => PermTimes(f(e0), f(e1))
      case ast.IntPermTimes(e0, e1) => IntPermTimes(f(e0), f(e1))
      case ast.PermLE(e0, e1) => AtMost(f(e0), f(e1))
      case ast.PermLT(e0, e1) => Less(f(e0), f(e1))
      case ast.PermGE(e0, e1) => AtLeast(f(e0), f(e1))
      case ast.PermGT(e0, e1) => Greater(f(e0), f(e1))

      /* Sequences */

      case silver.ast.SeqAppend(e0, e1) => SeqAppend(f(e0), f(e1))
      case silver.ast.SeqContains(e0, e1) => SeqIn(f(e1), f(e0))
      case silver.ast.SeqDrop(e0, e1) => SeqDrop(f(e0), f(e1))
      case silver.ast.SeqIndex(e0, e1) => SeqAt(f(e0), f(e1))
      case silver.ast.SeqLength(e) => SeqLength(f(e))
      case silver.ast.SeqTake(e0, e1) => SeqTake(f(e0), f(e1))
      case silver.ast.EmptySeq(typ) => SeqNil(toSort(typ, Map()))
      case silver.ast.RangeSeq(e0, e1) => SeqRanged(f(e0), f(e1))
      case silver.ast.SeqUpdate(e0, e1, e2) => SeqUpdate(f(e0), f(e1), f(e2))

      case silver.ast.ExplicitSeq(es) =>
        es.tail.foldLeft[SeqTerm](SeqSingleton(f(es.head)))((tSeq, e) =>
          SeqAppend(SeqSingleton(f(e)), tSeq))

      /* Sets and multisets */

      case silver.ast.EmptySet(typ) => EmptySet(toSort(typ, Map()))
      case silver.ast.EmptyMultiset(typ) => EmptyMultiset(toSort(typ, Map()))

      case silver.ast.ExplicitSet(es) =>
        es.tail.foldLeft[SetTerm](SingletonSet(f(es.head)))((tSet, e) =>
          SetAdd(tSet, f(e)))

      case silver.ast.ExplicitMultiset(es) =>
        es.tail.foldLeft[MultisetTerm](SingletonMultiset(f(es.head)))((tMultiset, e) =>
          MultisetAdd(tMultiset, f(e)))

      case as: silver.ast.AnySetUnion => translateAnySetBinExp(as, SetUnion, MultisetUnion)
      case as: silver.ast.AnySetIntersection => translateAnySetBinExp(as, SetIntersection, MultisetIntersection)
      case as: silver.ast.AnySetSubset => translateAnySetBinExp(as, SetSubset, MultisetSubset)
      case as: silver.ast.AnySetMinus => translateAnySetBinExp(as, SetDifference, MultisetDifference)
      case as: silver.ast.AnySetContains => translateAnySetBinExp(as, SetIn, MultisetIn, as.right)
      case as: silver.ast.AnySetCardinality => translateAnySetUnExp(as, SetCardinality, MultisetCardinality)

      /* Unsupported (because unexpected) expressions */

      case   _: ast.LocationAccess | _: ast.AccessPredicate | _: ast.Old | _: ast.FractionalPerm
             | _: ast.ResultLiteral | _: ast.Unfolding | _: ast.InhaleExhale | _: ast.PredicateAccess
             | _: ast.FuncApp | _: ast.CurrentPerm | _: ast.EpsilonPerm  | _: ast.WildcardPerm | _: ast.EpsilonPerm =>

        sys.error(s"Found unexpected expression $exp (${exp.getClass.getName}})")
    }
  }
}
