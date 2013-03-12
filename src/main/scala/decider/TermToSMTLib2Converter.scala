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

    case FApp(f, s, t0, tArgs, _) =>
      "(" + sanitiseIdentifier(f.name) + (s +: t0 +: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"

    case Quantification(quant, qvar, body) =>
      var strVar = "(%s %s)".format(qvar.id, convert(qvar.sort))
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

//    case SeqEq(t0, t1) =>
//      "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
//    //      "(= " + convert(t0) + " " + convert(t1) + ")"

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
    case ReadPerm(v) => convert(v)
    case TermPerm(t) => convert2real(t)
    case ConcPerm(n, d) => (n.toDouble / d.toDouble).toString

    case InternalRdPerm() => "$Perm.iRd"
    case MonitorRdPerm() => "$Perm.mRd"
    case PredicateRdPerm() => "$Perm.pRd"
    case ChannelRdPerm() => "$Perm.cRd"

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

//    /* Sequences */
//
//    case RangeSeq(t0, t1) =>
//      "($Seq.rng " + convert(t0) + " " + convert(t1) + ")"
//
//    //		case SeqElem(t0) => "(insert " + convert(t0) + " (as nil " + convert(term.sort) + "))"
//    case SeqElem(t0) => "($Seq.elem " + convert(t0) + ")"
//
//    case SeqCon(t0, t1) =>
//      "($Seq.con " + convert(t0) + " " + convert(t1) + ")"
//
//    case SeqLen(t0) => "($Seq.len " + convert(t0) + ")"
//
//    case SeqAt(t0, t1) =>
//      "($Seq.at " + convert(t0) + " " + convert(t1) + ")"
//
//    // case SeqSeg(t0, t1, t2) =>
//    // "($Seq.seg " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"
//
//    case SeqTake(t0, t1) =>
//      "($Seq.take " + convert(t0) + " " + convert(t1) + ")"
//
//    case SeqDrop(t0, t1) =>
//      "($Seq.drop " + convert(t0) + " " + convert(t1) + ")"
//
//    case SeqIn(t0, t1) =>
//      "($Seq.in " + convert(t0) + " " + convert(t1) + ")"
//
//    /* Monitors, Locks */
//
//    case LockLess(t0, t1) =>
//      "($Locks.less " + convert(t0) + " " + convert(t1) + ")"
//
//    //		case MaxLockLess(t0, hn, mn, cn) =>
//    //			"($Locks.maxlock.less %s %s %s %s)".format(convert(t0), hn, mn, cn)
//    case MaxLockLess(others, _, mu) =>
//      if (others.nonEmpty) (
//        others.map{m => "($Locks.less %s %s)".format(convert(m), convert(mu))}
//          .mkString("(and ", " ", ")"))
//      else
//        literalToString(True())
//
//    case MaxLockAtMost(others, _, mu) =>
//      if (others.nonEmpty)
//        others.map{m =>
//          val mStr = convert(m)
//          val muStr = convert(mu)
//          "(or ($Locks.less %1$s %2$s) (= %1$s %2$s))".format(mStr, muStr)
//        }.mkString("(and ", " ", ")")
//      else
//        literalToString(True())
//
//    //		case MaxLockAtMost(t0, hn, mn, cn) =>
//    //			"($Locks.maxlock.atMost %s %s %s %s)".format(convert(t0), hn, mn, cn)
//
//    //		case Holds(t, n, lm) =>
//    //			"(= ($Locks.holds %s %s) %s)".format(convert(t), n, lockModeToString(lm))
//    //    case Holds(rcvr, mu) =>
//    //      "($Locks.holds %s %s)".format(convert(rcvr), convert(mu))
//
//    case InitialHolds(rcvr) =>
//      "($Locks.initialHolds %s)".format(convert(rcvr))
//
//    case InitialMu(rcvr) =>
//      "($Locks.initialMu %s)".format(convert(rcvr))
//
//    //		case LockChange(which, n1, n2) =>
//    //			val r = Var("r", sorts.Ref)
//    //			val slhs = convert(BigAnd(which, t => r !== t))
//    //
//    //			("(forall ((r $Ref))" +
//    //					"(implies " +
//    //						"%s " +
//    //						"(= ($Locks.holds r %s) ($Locks.holds r %s))))"
//    //			).format(slhs, n1, n2)
//    //
//    //		case Mu(t0, mn, t1) =>
//    //			"(= ($Locks.mu %s %s) %s)".format(convert(t0), mn, convert(t1))
//
//    /* Credits */
//
//    case Credits(t0, cn) =>
//      "($Credits.credits %s %s)".format(convert(t0), cn)
//
//    case DebtFreeExpr(cn) =>
//      ("(forall ((r $Ref))" +
//        "(>= ($Credits.credits r %s) 0)" +
//        ")").format(cn)
//    //    case DebtFreeExpr(cn) =>
//    //      ("(forall ((r $Ref))" +
//    //        "(>= ($Credits.credits r %s) 0)" +
//    //        ":pat {($Credits.credits r %s)}" +
//    //        ")").format(cn, cn)

    /* Immutability */

//    case Immutable(t, id) => "($Immutability.immutable %s %s)".format(convert(t), math.abs(id.hashCode))
//    case Frozen(t, id) => "($Immutability.frozen %s %s)".format(convert(t), math.abs(id.hashCode))

    /* Auxiliary terms */

//    case UpdateMap(id, t, n) => "true"
//    //			val fctUpdate = id match {
//    //				case LockSupport.Holds => "$Locks.holds.updated"
//    //				case LockSupport.Mu => "$Locks.mu.updated"
//    //				case CreditSupport.Credits => "$Credits.credits.updated"
//    //				case _ => sys.error("Unknown map id found.") // id
//    //			}
//    //
//    //			"(%s %s %s)".format(fctUpdate, convert(t), n)

    case TypeOf(t: Term, typeName: String) =>
      "(= ($Type.typeOf %s) %s)".format(convert(t), typeName)

    case SnapEq(t0, t1) =>
      "($Snap.snapEq " + convert(t0) + " " + convert(t1) + ")"

    case First(t) => "($Snap.first " + convert(t) + ")"
    case Second(t) => "($Snap.second " + convert(t) + ")"

    case Combine(t0, t1) =>
      "($Snap.combine " + convert(t0) + " " + convert(t1) + ")"

//    case SortWrapper(t, sort) =>
//      "($sorts.%sTo%s %s)".format(sortToWrapperName(t.sort), sortToWrapperName(sort), convert(t))
    /* These sorts are converted to Z3-sort Int anyway */
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

//  private def sortToWrapperName(sort: Sort) = sort match {
//    //    case sorts.Seq(s) => "List<" + convert(s) + ">"
//    case _ => convert(sort)
//  }

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