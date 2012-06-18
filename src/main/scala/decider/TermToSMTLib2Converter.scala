package ch.ethz.inf.pm.silicon
package decider

import silAST.programs.symbols.{Function => SILFunction}

// import ch.ethz.inf.pm.silicon
import interfaces.decider.TermConverter
import state.terms._
// import state.terms.utils.SetAnd

/* TODO: Unify terms.And and DomainFApp("∧"), such that only one of them,
 *       probably the latter, is used by Silicon.
 */

class TermToSMTLib2Converter extends TermConverter[String, String] {
  def convert(term: Term): String = term match {
		case Var(id: String, _) => sanitiseIdentifier(id)
		case lit: Literal => literalToString(lit)

		// case Ite(t0, t1, t2) =>
			// "(ite " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

		case FApp(f, s, t0, tArgs, _) =>
			// "(" + f.fullName + (s :: t0 :: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"
			"(" + sanitiseIdentifier(f.name) + (s +: t0 +: tArgs).map(convert(_)).mkString(" ", " ", "") + ")"
			
		case Quantification(quant, qvar, body) =>
			// val strVars =
        // tVars.map(v => "(%s %s)".format(v.id, convert(v.sort))).mkString(" ")
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
			
		// case SeqEq(t0, t1) =>
			// "($Seq.eq " + convert(t0) + " " + convert(t1) + ")"
			
    /* Expects both arguments to be of the same sort. */
		case Eq(t0, t1) => t0.sort match {
      case sorts.Snap =>
        "($snapEq " + convert(t0) + " " + convert(t1) + ")"
      case _ =>
        "(= " + convert(t0) + " " + convert(t1) + ")"
    }

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

		/* Sequences */

		// case RangeSeq(t0, t1) =>
			// "($Seq.rng " + convert(t0) + " " + convert(t1) + ")"
			
		// case SeqElem(t0) => "($Seq.elem " + convert(t0) + ")"
		
		// case SeqCon(t0, t1) =>
			// "($Seq.con " + convert(t0) + " " + convert(t1) + ")"
			
		// case SeqLen(t0) => "($Seq.len " + convert(t0) + ")"
		
		// case SeqAt(t0, t1) =>
			// "($Seq.at " + convert(t0) + " " + convert(t1) + ")"
			
		// // case SeqSeg(t0, t1, t2) =>
			// // "($Seq.seg " + convert(t0) + " " + convert(t1) + " " + convert(t2) + ")"

		// case SeqTake(t0, t1) =>
			// "($Seq.take " + convert(t0) + " " + convert(t1) + ")"
			
		// case SeqDrop(t0, t1) =>
			// "($Seq.drop " + convert(t0) + " " + convert(t1) + ")"
			
		// case SeqIn(t0, t1) =>
			// "($Seq.in " + convert(t0) + " " + convert(t1) + ")"
			
		/* Monitors, Locks */

		// case LockLess(t0, t1) =>
			// "($Locks.less " + convert(t0) + " " + convert(t1) + ")"
      
		// case MaxLockLess(t0, hn, mn, cn) =>
			// "($Locks.maxlock.less %s %s %s %s)".format(convert(t0), hn, mn, cn)
      
		// case MaxLockAtMost(t0, hn, mn, cn) =>
			// "($Locks.maxlock.atMost %s %s %s %s)".format(convert(t0), hn, mn, cn)
			
		// case Holds(t, n, p) =>
			// "(= ($Locks.holds %s %s) %s)".format(convert(t), n, convert(p))
			
		// case LockMode.Read => "$Locks.mode.read"
		// case LockMode.Write => "$Locks.mode.write"
		// case LockMode.None => "$Locks.mode.none"			

		// case LockChange(which, n1, n2) =>
			// val r = Var("r", IntSort)
			// val slhs = convert(SetAnd(which, t => Not(TermEq(r, t))))
			
			// ("(forall ((r Int))" +
					// "(implies " +
						// "%s " + 
						// "(= ($Locks.holds r %s) ($Locks.holds r %s))))"
			// ).format(slhs, n1, n2)
			
		// case Mu(t0, mn, t1) =>
			// "(= ($Locks.mu %s %s) %s)".format(convert(t0), mn, convert(t1))

		/* Credits */
			
		// case Credits(t0, cn) =>
			// "($Credits.credits %s %s)".format(convert(t0), cn)
			
		// case DebtFreeExpr(cn) =>
			// ("(forall ((r Int))" +
					// "(>= ($Credits.credits r %s) 0))").format(cn)
			
		/* Permissions */
    
    case FullPerms() => "$Perms.Write"
    case ZeroPerms() => "$Perms.Zero"
    case PercPerms(n) => (n / 100.0).toString
    case Perms(t) => convert(t)

		case PermMinus(t0, t1) =>
			"(- " + convert2real(t0) + " " + convert2real(t1) + ")"

		case PermPlus(t0, t1) =>
			"(+ " + convert2real(t0) + " " + convert2real(t1) + ")"

		case PermTimes(t0, t1) =>
			"(* " + convert2real(t0) + " " + convert2real(t1) + ")"

    case IntPermTimes(t0, t1) =>
      "(* " + convert2real(t0) + " " + convert2real(t1) + ")"

    case PermLess(t0, t1) =>
      "(< " + convert(t0) + " " + convert(t1) + ")"
    
    /* Domains */
    
    // case DomainPApp(dp, ts) => dp match {
      // case silAST.types.booleanEvaluate => convert(ts(0))
    // }
    
    // case DomainPApp(dp, ts) => (dp.name, ts) match {
      // case ("eval", t0 :: Nil) => convert(t0)
    // }
    
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

      if (ts.isEmpty)
        sid
      else
        "(%s %s)".format(sid, argsStr)
      // val funId = 
      
      // sys.error("Found unsupported %s".format(term))
      
      // f match {
      // case silAST.types.booleanTrue => "true"
      // case silAST.types.booleanFalse => "false"
      // case silAST.types.booleanNegation => "(not %s)".format(convert(ts(0)))
      // case silAST.types.booleanConjunction => "(and %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.booleanDisjunction => "(or %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.booleanImplication => "(implies %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.booleanEquivalence => "(iff %s %s)".format(convert(ts(0)), convert(ts(1)))
      
      // case silAST.types.nullFunction => "$null"
      // case silAST.types.referenceEquality => "(= %s %s)".format(convert(ts(0)), convert(ts(1)))
      
      // case silAST.types.integerAddition => "(+ %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.integerSubtraction => "(- %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.integerMultiplication => "(* %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.integerDivision => "(/ %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.integerModulo => "(% %s %s)".format(convert(ts(0)), convert(ts(1)))
      // case silAST.types.integerNegation => "(- 0 %s)".format(convert(ts(0)))
    // }
    
    // case DomainFApp(f, ts, sort) => (f.name, ts) match {
      // /* Boolean */
      // case ("true", Nil) => "true"
      // case ("false", Nil) => "false"      
      // case ("!", t0 :: Nil) => "(not " + convert(t0) + ")"
      // case ("∧", t0 :: t1 :: Nil) => "(and " + convert(t0) + " " + convert(t1) + ")"
      // case ("∨", t0 :: t1 :: Nil) => "(or " + convert(t0) + " " + convert(t1) + ")"
      // case ("→", t0 :: t1 :: Nil) => "(==> " + convert(t0) + " " + convert(t1) + ")"
      // case ("↔", t0 :: t1 :: Nil) => "(<==> " + convert(t0) + " " + convert(t1) + ")"
        
      // /* Integers */

      // case ("*", t0 :: t1 :: Nil) => "(* " + convert(t0) + " " + convert(t1) + ")"
      // case ("+", t0 :: t1 :: Nil) => "(+ " + convert(t0) + " " + convert(t1) + ")"
      // case ("-", t0 :: t1 :: Nil) => "(- " + convert(t0) + " " + convert(t1) + ")"
      
      // /* Integers */
      
      // case ("null", Nil) => "$null"
    // }
    
		/* Auxiliary terms */

		// case UpdateMap(id, t, n) =>
			// val fctUpdate = id match {
				// // case LockSupport.Holds => "$Locks.holds.updated"
				// // case LockSupport.Mu => "$Locks.mu.updated"
				// // case CreditSupport.Credits => "$Credits.credits.updated"
				// case _ => sys.error("Unknown map id found.") // id
			// }
			
			// "(%s %s %s)".format(fctUpdate, convert(t), n)
		
		case Combine(t0, t1) =>
			"($combine " + convert(t0) + " " + convert(t1) + ")"
			
		// case SnapEq(t0, t1) =>
			// "($snapEq " + convert(t0) + " " + convert(t1) + ")"

		// case BoolToInt(t0) => "($boolToInt " + convert(t0) + ")"
		// case IntToBool(t0) => "($intToBool " + convert(t0) + ")"
		
		/* These sorts are converted to Z3-sort Int anyway */
    case SortWrapper(t, sort) =>
      "($sorts.%sTo%s %s)".format(convert(t.sort), convert(sort), convert(t))
		// case SeqToInt(t0) => convert(t0)
		// case IntToSeq(t0) => convert(t0)
		// case MuToInt(t0) => convert(t0)
		// case IntToMu(t0) => convert(t0)
  }

	def convert(sort: Sort) = sort match {
		case sorts.Int => "Int"
		case sorts.Bool => "Bool"
		case sorts.Perms => "$Perms"
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
			
		case Unit => "$unit"
		case True() => "true"
		case False() => "false"
		case Null() => "$null"
		// case EmptySeq() => "$Seq.nil"
		// case BottomLock() => "$Locks.bottom"
	}
  
  // @annotation.elidable(annotation.elidable.OFF)
  // private def assertLength(ts: Seq[_], l: Int, o: AnyRef) {
    // assert(ts.length == l, "Expected %s argument to %s, but found %s".format(l, o, ts.length))
  // }
  
  // /* TODO: Seems more senseful to work on ast....DataTypes than on Domains */
  // private def convert(d: silAST.domains.Domain) = {
    // // println("  d = " + d)
    // // println("  d.getClass.getName = " + d.getClass.getName)
    // // println("  d.freeTypeVariables = " + d.freeTypeVariables)
    // // println("  d.getType = " + d.getType)  
  // (
    // d.fullName.replace('[', '<')
              // .replace(']', '>')
              // .replace(',', '~'))
              // /* TODO: Get Domain from UserSort, use TypeConverter to convert parameter types. */
              // // .replace("Integer", "Int")
              // // .replace("Permission", "$Perms")
              // // .replace("ref", "$Ref"))
  // }

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