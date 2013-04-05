package semper
package silicon
package decider

import interfaces.decider.TermConverter
import state.terms._

class TermToSMTLib2Converter extends TermConverter[String, String] {
  def convert(term: Term): String = term match {
    case Var(id: String, _) => sanitiseIdentifier(id)
    case lit: Literal => literalToString(lit)

    case Ite(t0, t1, t2) =>
      "(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

    case FApp(f, s, tArgs, _) =>
      "(%s %s %s)".format(sanitiseIdentifier(f.name), convert(s), tArgs map convert mkString(" "))

    case Quantification(quant, qvar, body) =>
      val strVar = "(%s %s)".format(qvar.id, convert(qvar.sort))
      val strBody = convert(body)

      "(%s (%s) %s)".format(convert(quant), strVar, strBody)

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

    /* Equalities */

    case TermEq(t0, t1) =>
      "(= " + convert(t0) + " " + convert(t1) + ")"

    /* Arithmetics */

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

    case pt: PermissionsTuple => convert(pt.combined)

    case FullPerm() => "$Perm.Write"
    case NoPerm() => "$Perm.No"
    case StarPerm(v) => convert(v)
//    case ReadPerm(v) => convert(v)
    case TermPerm(t) => convert2real(t)
    case ConcretePerm(n, d) => (n.toDouble / d.toDouble).toString

//    case InternalRdPerm() => "$Perm.iRd"
//    case MonitorRdPerm() => "$Perm.mRd"
//    case PredicateRdPerm() => "$Perm.pRd"
//    case ChannelRdPerm() => "$Perm.cRd"

    case IsValidPerm(v, ub) =>
      "($Perm.isValid %s %s)".format(convert(v), convert(ub))

    case IsReadPerm(v, ub) =>
      "($Perm.isRead %s %s)".format(convert(v), convert(ub))

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

    /* Domains */

    case DomainFApp(id, ts, sort) =>
      // println("\n[TermToSMTLib2Converter/DomainFApp]")
      // println("  f = " + f)
      // println("  f.domain = " + f.domain)
      // println("  f.domain.freeTypeVariables = " + f.domain.freeTypeVariables)
      // println("  f.domain.getType = " + f.domain.getType)
      // println("  ts = " + ts)
      // println("  sort = " + sort)

      // val domainStr = convert(f.domain)
      val argsStr = ts.map(convert).mkString(" ")
      val sid = sanitiseIdentifier(id)

      if (ts.isEmpty) sid
      else "(%s %s)".format(sid, argsStr)

    case TypeOf(t: Term, typeName: String) =>
      "(= ($Type.typeOf %s) %s)".format(convert(t), typeName)

    case SnapEq(t0, t1) =>
      "($Snap.snapEq " + convert(t0) + " " + convert(t1) + ")"

    case First(t) => "($Snap.first " + convert(t) + ")"
    case Second(t) => "($Snap.second " + convert(t) + ")"

    case Combine(t0, t1) =>
      "($Snap.combine " + convert(t0) + " " + convert(t1) + ")"

    case SortWrapper(t, sort) =>
      "($SortWrappers.%sTo%s %s)".format(convert(t.sort), convert(sort), convert(t))
  }

  def convert(sort: Sort) = sort match {
    case sorts.Int => "Int"
    case sorts.Bool => "Bool"
    case sorts.Perm => "$Perm"
    case sorts.Snap => "$Snap"
    case sorts.Ref => "$Ref"
    case sorts.UserSort(id) => sanitiseIdentifier(id)
  }

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
  }

  private def convert2real(t: Term): String =
    if (t.sort == sorts.Int)
      "(to_real " + convert(t) + ")"
    else
      convert(t)

  def sanitiseIdentifier(str: String) = (
    str.replace('#', '_')
      .replace("τ", "$tau")
      .replace('[', '<')
      .replace(']', '>')
      .replace("::", ".")
      .replace(',', '~'))
}
