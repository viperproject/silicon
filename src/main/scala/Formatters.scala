package semper
package silicon

import interfaces.state.{Store, Heap, State, StateFormatter}
import decider.TermToSMTLib2Converter
import state.DefaultTypeConverter
import state.terms._

class DefaultStateFormatter[ST <: Store[ST], H <: Heap[H], S <: State[ST, H, S]]
    extends StateFormatter[ST, H, S, String] {
			
  def format(σ: S) = {
		val γ = format(σ.γ)			
		val h = format(σ.h, "h")
		val g = format(σ.g, "g")
		val π = format(σ.π)
		
		"σ(\n  %s, \n  %s, \n  %s, \n  %s\n)".format(γ, h, g, π)
	}
	
	def format(γ: ST) = {
		val map = γ.values
		if (map.isEmpty) "Ø" else "γ" + map.mkString("(", ", ", ")")
	}
	
	def format(h: H) = format(h, "h")
	
	private def format(h: H, id: String) = {
		val values = h.values
		if (values.isEmpty) "Ø" else id + values.mkString("(", ", ", ")")
	}
	
	def format(π: Set[Term]) = {
		/* Attention: Hides non-null and combine terms. */
		if (π.isEmpty) "Ø"
		else
			"π" + (π.filterNot {
				case c: Eq if    c.p0.isInstanceOf[Combine]
														|| c.p1.isInstanceOf[Combine] => true
				case Not(TermEq(_, Null())) => true
				case _ => false
			}).mkString("(", ", ", ")")	
	}
}

//class SMT2PathConditionFormatter() {
//	val termConverter = new TermToSMTLib2Converter()
//	val typeConverter = new DefaultTypeConverter()
//
//	def format(π: Iterable[Term]): String = {
//    val str = """
//;
//; Function declarations
//;
//%s
//
//;
//; Constant declarations
//;
//%s
//
//;
//; Assumptions
//;
//%s
//
//(push)
//(check-sat)
//(pop)
//"""
//
//		val vs = π.flatMap(getVars).toSet.map((v: Var) =>
//			"(declare-fun %s () %s)".format(v.id, termConverter.convert(v.sort)))
//
//		val fs = π.flatMap(getFuncs).toSet.map((f: ast.Function) =>
//			"(declare-fun %s (Int Int %s) %s)".format(
//					f.fullName,
//					f.ins map (v =>
//						termConverter.convert(typeConverter.toSort(v.t))) mkString(" "),
//					termConverter.convert(typeConverter.toSort(f.out))))
//
//		val as = π map termConverter.convert map (a => "(assert " + a + ")")
//
//		str.format(fs.mkString("\n"), vs.mkString("\n"), as.mkString("\n"))
//	}
//
//	def logPathConditions(π: Set[Term], file: String) {
//		import java.io.{PrintWriter, BufferedWriter, FileWriter, File}
//
//		val dest =
//			new PrintWriter(
//					new BufferedWriter(new FileWriter(new File(file))), true)
//
//		dest.println(format(π))
//		dest.close()
//	}
//
//	private def getVars(t: Term): List[Var] = t match {
//		case v: Var => List(v)
//		case Combine(t0, t1) => getVars(t0) ::: getVars(t1)
//		case sw: SortWrapper => getVars(sw.t)
//		case uo: ast.commonnodes.UnaryOp[Term] => getVars(uo.p)
//		case bo: ast.commonnodes.BinaryOp[Term] =>
//			getVars(bo.p0) ::: getVars(bo.p1)
//		case Ite(t0, t1, t2) => getVars(t0) ::: getVars(t1) ::: getVars(t2)
//		case FApp(_, s, t0, tArgs, _) =>
//			getVars(s) ::: getVars(t0) ::: (tArgs flatMap getVars)
//		case Quantification(_, tVars, tBody) =>
//			getVars(tBody) ::: (tVars flatMap getVars)
//		case _ => Nil
//	}
//
//	private def getFuncs(t: Term): List[ast.Function] = t match {
//		case Combine(t0, t1) => getFuncs(t0) ::: getFuncs(t1)
//		case sw: SortWrapper => getFuncs(sw.t)
//		case uo: ast.commonnodes.UnaryOp[Term] => getFuncs(uo.p)
//		case bo: ast.commonnodes.BinaryOp[Term] =>
//			getFuncs(bo.p0) ::: getFuncs(bo.p1)
//		case Ite(t0, t1, t2) =>
//			getFuncs(t0) ::: getFuncs(t1) ::: getFuncs(t2)
//		case FApp(f, s, t0, tArgs, _) =>
//			f :: getFuncs(s) ::: getFuncs(t0) ::: (tArgs flatMap getFuncs)
//		case Quantification(_, _, tBody) => getFuncs(tBody)
//		case _ => Nil
//	}
//}