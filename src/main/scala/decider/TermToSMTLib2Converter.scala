package semper
package silicon
package decider

import interfaces.decider.TermConverter
import state.terms._

class TermToSMTLib2Converter extends TermConverter[String, String, String] {
  def convert(sort: Sort): String = sort match {
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
    case sorts.Unit =>
      /* Sort Unit corresponds to Scala's Unit type and is used, e.g., as the
       * domain sort of nullary functions.
       */
      ""

    /* [SNAP-EQ] */
//    case a: sorts.Array => s"(Array ${convert(a.from)} ${convert(a.to)})"
//    case a: sorts.Array => s"Array<${convert(a.from)}~${convert(a.to)}>"
  }

  def convert(decl: Decl): String = decl match {
    case SortDecl(sort: Sort) =>
      "(declare-sort %s)".format(convert(sort))

    case FunctionDecl(Function(id, sort)) =>
      val idStr = sanitizeSymbol(id)
      val inSortStr = sort.inSorts.map(convert).mkString(" ")
      val outSortStr = convert(sort.outSort)

      s"(declare-fun $idStr ($inSortStr) $outSortStr)"

    case SortWrapperDecl(from, to) =>
      val symbol = sortWrapperSymbol(from, to)
      val fct = FunctionDecl(Function(symbol, from :: Nil, to))
      convert(fct)
  }

  def convert(term: Term): String = term match {
    case s: Symbol => sanitizeSymbol(s.id)
    case lit: Literal => literalToString(lit)

    case Ite(t0, t1, t2) =>
      "(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

    case FApp(f, s, tArgs) =>
      "(%s %s %s)".format(sanitizeSymbol(f.id), convert(s), tArgs map convert mkString " ")

    case Quantification(quant, vars, body, triggers) =>
      val strVars = vars map (v => s"(${v.id} ${convert(v.sort)})") mkString " "
      val strBody = convert(body)
      val strQuant = convert(quant)

      val strTriggers: String =
        triggers.map(trigger => trigger.ts map convert mkString " ")
                .map(s => s":pattern ($s)")
                .mkString(" ")

      "(%s (%s) (! %s %s))".format(strQuant, strVars, strBody, strTriggers)

    /* Booleans */

    case NullTrigger(t) => "($Ref.nullTrigger " + convert(t) + ")"

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

    case Eq(t0, t1, specialise) =>
      /* Design choice: Either have a single Eq term, and based on its sort,
       * different equalities are generated on the SMTLib2 level. This is
       * currently done, but has the disadvantage, that the additional
       * specialise flag is needed to indicate when to generate user-defined
       * equality, e.g., $Snap.eq, or built-in equality, i.e., "=".
       * Another possible design is to have equality terms for each sort, e.g.,
       * SnapEq and SeqEq, and a general one, e.g., Eq, that always translates
       * to built-in equality. This approach has the disadvantage, that
       * an additional case distinction is necessary when SIL equalities are
       * translated to Silicon terms.
       */

      if (specialise)
        t0.sort match {
          case sorts.Snap => convertBuiltinEq(t0, t1) // "(= " + convert(t0) + " " + convert(t1) + ")"
          case _: sorts.Seq => "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
          case _: sorts.Set => "($Set.eq " + convert(t0) + " " + convert(t1) + ")"
          case _ => "(= " + convert(t0) + " " + convert(t1) + ")"
        }
      else
        convertBuiltinEq(t0, t1)
//        "(= " + convert(t0) + " " + convert(t1) + ")"


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

    case First(t) => "($Snap.first " + convert(t) + ")"
    case Second(t) => "($Snap.second " + convert(t) + ")"

    case combine @ Combine(t0, t1) =>
      "($Snap.combine " + convert(t0) + " " + convert(t1) + ")"

    case SortWrapper(t, to) =>
      "(%s %s)".format(sortWrapperSymbol(t.sort, to), convert(t))

    case Distinct(symbols) =>
      "(distinct %s)".format(symbols map convert  mkString " ")

    /* [SNAP-EQ] */
    case Select(t0, t1) =>
//      s"(select ${convert(t0)} ${convert(t1)})"
      s"(${convert(t0)} ${convert(t1)})"
  }

  def sanitizeSymbol(str: String) =
    str.replace('#', '_')
       .replace("τ", "$tau")
       .replace('[', '<')
       .replace(']', '>')
       .replace("::", ".")
       .replace(',', '~')
       .replace(" ", "")

  private def convert(q: Quantifier) = q match {
    case Forall => "forall"
    case Exists => "exists"
  }

  private def literalToString(literal: Literal) = literal match {
    case IntLiteral(n) =>
      if (n >= 0) n.toString()
      else "(- 0 %s)".format((-n).toString())

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

  /* [SNAP-EQ] */
  private def sortWrapperSymbol(from: Sort, to: Sort) =
    "$SortWrappers.%sTo%s".format(convert(from), convert(to))
//    s"$$SortWrappers.${sortWrapperSortSymbol(from)}To${sortWrapperSortSymbol(to)}"

//  private def sortWrapperSortSymbol(sort: Sort): String = sort match {
//    case sorts.Array(from, to) => s"Array<${sortWrapperSortSymbol(from)}~${sortWrapperSortSymbol(to)}>"
//    case _ => convert(sort)
//  }

  private def convertBuiltinEq(t0: Term, t1: Term): String = {
    val hasStar = (t0 existsDefined { case *() => }) || (t1 existsDefined { case *() => })

    if (hasStar) {
      val x = Var("x", sorts.Ref)
      val t0a = t0.replace(*(), x)
      val t1a = t1.replace(*(), x)
      s"(forall ((x $$Ref)) (= ${convert(t0a)} ${convert(t1a)}))"
    } else
      s"(= ${convert(t0)} ${convert(t1)})"
  }
}
