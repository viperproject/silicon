package semper
package silicon
package decider

import interfaces.decider.TermConverter
import semper.silicon.state.terms._
import semper.silicon.state.terms.Mod
import semper.silicon.state.terms.IsValidPermVar
import semper.silicon.state.terms.DomainFApp
import semper.silicon.state.terms.FullPerm
import semper.silicon.state.terms.False
import semper.silicon.state.terms.SingletonSet
import semper.silicon.state.terms.TermPerm
import semper.silicon.state.terms.First
import semper.silicon.state.terms.IsReadPermVar
import semper.silicon.state.terms.Eq
import semper.silicon.state.terms.Combine
import semper.silicon.state.terms.FunctionDecl
import semper.silicon.state.terms.SortWrapper
import semper.silicon.state.terms.True
import semper.silicon.state.terms.SeqSingleton
import semper.silicon.state.terms.IntLiteral
import semper.silicon.state.terms.Null
import semper.silicon.state.terms.FApp
import semper.silicon.state.terms.EmptySet
import semper.silicon.state.terms.NoPerm
import semper.silicon.state.terms.Second
import semper.silicon.state.terms.PermMin
import semper.silicon.state.terms.Div
import semper.silicon.state.terms.SeqNil
import semper.silicon.state.terms.WildcardPerm
import semper.silicon.state.terms.SeqRanged
import semper.silicon.state.terms.SortWrapperDecl
import semper.silicon.state.terms.Quantification
import semper.silicon.state.terms.FractionPerm
import semper.silicon.state.terms.SortDecl

class TermToSMTLib2Converter extends TermConverter[String, String, String] {
  def convert(sort: Sort) = sort match {
    case sorts.Int => "Int"
    case sorts.Bool => "Bool"
    case sorts.Perm => "$Perm"
    case sorts.Snap => "$Snap"
    case sorts.Ref => "$Ref"
    case sorts.Seq(elementSort) => "$Seq<" + convert(elementSort) + ">"
    case sorts.Set(elementSort) => "$Set<" + convert(elementSort) + ">"
    case sorts.Multiset(elementSort) => "$Multiset<" + convert(elementSort) + ">"
    case sorts.UserSort(id) => sanitizeSymbol(id)
    case a: sorts.Arrow => "(%s) %s".format(a.inSorts.map(convert).mkString("(", " ", ")"), convert(a.outSort))
    case sorts.Unit => ""
  }

  def convert(decl: Decl): String = decl match {
    case SortDecl(sort: Sort) =>
      "(declare-sort %s)".format(convert(sort))

    case FunctionDecl(Function(id, sort)) =>
      "(declare-fun %s (%s) %s)".format(sanitizeSymbol(id), sort.inSorts.map(convert).mkString(" "), convert(sort.outSort))

    case SortWrapperDecl(from, to) =>
      val symbol = sortWrapperSymbol(from, to)
      convert(FunctionDecl(Function(symbol, from :: Nil, to)))
  }

  def convert(term: Term): String = term match {
    case s: Symbol => sanitizeSymbol(s.id)
    case lit: Literal => literalToString(lit)

    case Ite(t0, t1, t2) =>
      "(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

    case FApp(f, s, tArgs) =>
      "(%s %s %s)".format(sanitizeSymbol(f.id), convert(s), tArgs map convert mkString(" "))

    case Quantification(quant, vars, body) =>
      val strVars = vars map (v => s"(${v.id} ${convert(v.sort)})") mkString(" ")
      val strBody = convert(body)

      "(%s (%s) %s)".format(convert(quant), strVars, strBody)

    /* Booleans */

    case Not(f) => "(not " + convert(f) + ")"

    /* TODO: Extract common conversion behaviour of binary expressions. */

    case And(t0, t1) =>
      "(and " + convert(t0) + " " + convert(t1) + ")"

    case Or(t0, t1) =>
      "(or " + convert(t0) + " " + convert(t1) + ")"

    case Implies(t0, t1) =>
      "(implies " + convert(t0) + " " + convert(t1) + ")"

    case Iff(t0, t1) =>
      "(iff " + convert(t0) + " " + convert(t1) + ")"

    case Eq(t0, t1) => t0.sort match {
      case sorts.Snap => "($Snap.eq " + convert(t0) + " " + convert(t1) + ")"
      case _: sorts.Seq => "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
      case _: sorts.Set => "($Set.eq " + convert(t0) + " " + convert(t1) + ")"
      case _ => "(= " + convert(t0) + " " + convert(t1) + ")"
    }

    /* Arithmetic */

    case Minus(t0, t1) =>
      "(- " + convert(t0) + " " + convert(t1) + ")"

    case Plus(t0, t1) =>
      "(+ " + convert(t0) + " " + convert(t1) + ")"

    case Times(t0, t1) =>
      "(* " + convert(t0) + " " + convert(t1) + ")"

    case Div(t0, t1) =>
      "(div " + convert(t0) + " " + convert(t1) + ")"

    case Mod(t0, t1) =>
      "(mod " + convert(t0) + " " + convert(t1) + ")"

    /* Arithmetic comparisons */

    case Less(t0, t1) =>
      "(< " + convert(t0) + " " + convert(t1) + ")"

    case AtMost(t0, t1) =>
      "(<= " + convert(t0) + " " + convert(t1) + ")"

    case AtLeast(t0, t1) =>
      "(>= " + convert(t0) + " " + convert(t1) + ")"

    case Greater(t0, t1) =>
      "(> " + convert(t0) + " " + convert(t1) + ")"

    /* Permissions */

    case FullPerm() => "$Perm.Write"
    case NoPerm() => "$Perm.No"
    case WildcardPerm(v) => convert(v)
//    case EpsilonPerm() => "$Perm.Eps"
    case TermPerm(t) => convert2real(t)
    case FractionPerm(n, d) => "(/ %s %s)".format(convert2real(n), convert2real(d))

    case IsValidPermVar(v) =>
      "($Perm.isValidVar %s)".format(convert(v))

    case IsReadPermVar(v, ub) =>
      "($Perm.isReadVar %s %s)".format(convert(v), convert(ub))

    case PermLess(t0, t1) =>
      "(< %s %s)".format(convert(t0), convert(t1))

    case PermPlus(t0, t1) =>
      "(+ %s %s)".format(convert2real(t0), convert2real(t1))

    case PermMinus(t0, t1) =>
      "(- %s %s)".format(convert2real(t0), convert2real(t1))

    case PermTimes(t0, t1) =>
      "(* %s %s)".format(convert2real(t0), convert2real(t1))

    case IntPermTimes(t0, t1) =>
      "(* %s %s)".format(convert2real(t0), convert2real(t1))

    case PermMin(t0, t1) =>
      "($Perm.min %s %s)".format(convert(t0), convert(t1))
    /* Sequences */

//    case SeqEq(t0, t1) =>
//      "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"

    case SeqRanged(t0, t1) =>
      "($Seq.rng " + convert(t0) + " " + convert(t1) + ")"

    case SeqSingleton(t0) => "($Seq.elem " + convert(t0) + ")"

    case SeqAppend(t0, t1) =>
      "($Seq.con " + convert(t0) + " " + convert(t1) + ")"

    case SeqLength(t0) => "($Seq.len " + convert(t0) + ")"

    case SeqAt(t0, t1) =>
      "($Seq.at " + convert(t0) + " " + convert(t1) + ")"

    case SeqTake(t0, t1) =>
      "($Seq.take " + convert(t0) + " " + convert(t1) + ")"

    case SeqDrop(t0, t1) =>
      "($Seq.drop " + convert(t0) + " " + convert(t1) + ")"

    case SeqIn(t0, t1) =>
      "($Seq.in " + convert(t0) + " " + convert(t1) + ")"

    case SeqUpdate(t0, t1, t2) =>
      s"($$Seq.update ${convert(t0)} ${convert(t1)} ${convert(t2)})"

    /* Sets */

    case SingletonSet(t0) => "($Set.singleton " + convert(t0) + ")"
    case SetAdd(t0, t1) => "($Set.add " + convert(t0) + " " + convert(t1) + ")"
    case SetCardinality(t0) => "($Set.card " + convert(t0) + ")"
    case SetDifference(t0, t1) => "($Set.difference " + convert(t0) + " " + convert(t1) + ")"
    case SetIntersection(t0, t1) => "($Set.intersection " + convert(t0) + " " + convert(t1) + ")"
    case SetUnion(t0, t1) => "($Set.union " + convert(t0) + " " + convert(t1) + ")"
    case SetIn(t0, t1) => "($Set.in " + convert(t0) + " " + convert(t1) + ")"
    case SetSubset(t0, t1) => "($Set.subset " + convert(t0) + " " + convert(t1) + ")"
    case SetDisjoint(t0, t1) =>  "($Set.disjoint " + convert(t0) + " " + convert(t1) + ")"

    /* Multisets */

//    case SetAdd(t0, t1) => "($Set.add " + convert(t0) + " " + convert(t1) + ")"
    case MultisetCardinality(t0) => "($Multiset.card " + convert(t0) + ")"
    case MultisetDifference(t0, t1) => "($Multiset.difference " + convert(t0) + " " + convert(t1) + ")"
    case MultisetIntersection(t0, t1) => "($Multiset.intersection " + convert(t0) + " " + convert(t1) + ")"
    case MultisetUnion(t0, t1) => "($Multiset.union " + convert(t0) + " " + convert(t1) + ")"
    case MultisetIn(t0, t1) => "(> ($Multiset.count " + convert(t1) + " " + convert(t0) + ") 0)"
    case MultisetSubset(t0, t1) => "($Multiset.subset " + convert(t0) + " " + convert(t1) + ")"
    case MultisetCount(t0, t1) => "($Multiset.count " + convert(t1) + " " + convert(t0) + ")"
    case MultisetFromSeq(t0) => "($Multiset.fromSeq " + convert(t0) + ")"

    /* Domains */

    case DomainFApp(f, ts) =>
      val argsStr = ts.map(convert).mkString(" ")
      val sid = sanitizeSymbol(f.id)

      if (ts.isEmpty) sid
      else "(%s %s)".format(sid, argsStr)

    /* Other terms */

//    case SnapEq(t0, t1) =>
//      "($Snap.snapEq " + convert(t0) + " " + convert(t1) + ")"

    case First(t) => "($Snap.first " + convert(t) + ")"
    case Second(t) => "($Snap.second " + convert(t) + ")"

    case Combine(t0, t1) =>
      "($Snap.combine " + convert(t0) + " " + convert(t1) + ")"

    case SortWrapper(t, to) =>
      "(%s %s)".format(sortWrapperSymbol(t.sort, to), convert(t))

    case Distinct(symbols) =>
      "(distinct %s)".format(symbols map(convert) mkString(" "))
  }

  def sanitizeSymbol(str: String) = (
    str.replace('#', '_')
      .replace("τ", "$tau")
      .replace('[', '<')
      .replace(']', '>')
      .replace("::", ".")
      .replace(',', '~'))
      .replace(" ", "")

  private def convert(q: Quantifier) = q match {
    case Forall => "forall"
    case Exists => "exists"
  }

  private def literalToString(literal: Literal) = literal match {
    case IntLiteral(n) =>
      if (n >= 0) n.toString
      else "(- 0 %s)".format((-n).toString)

    case Unit => "$Snap.unit"
    case True() => "true"
    case False() => "false"
    case Null() => "$Ref.null"
    case SeqNil(elementSort) => "$Seq.nil<" + convert(elementSort) + ">"
    case EmptySet(elementSort) => "$Set.empty<" + convert(elementSort) + ">"
  }

  private def convert2real(t: Term): String =
    if (t.sort == sorts.Int)
      "(to_real " + convert(t) + ")"
    else
      convert(t)

  private def sortWrapperSymbol(from: Sort, to: Sort) =
    "$SortWrappers.%sTo%s".format(convert(from), convert(to))
}
