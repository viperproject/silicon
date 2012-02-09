package ch.ethz.inf.pm.silicon.state.terms

//import scala.util.parsing.input.{Position, NoPosition}
import silAST.{ASTNode => SILASTNode}
import silAST.source.{SourceLocation => SILSourceLocation, noLocation => SILNoLocation}
import silAST.programs.symbols.{Function => SILFunction}

import ch.ethz.inf.pm.silicon
// import silicon.ast
// import silicon.ast.commonnodes
// import silicon.ast.commonnodes.{UnaryOp, BinaryOp}
import silicon.interfaces.state.{Heap, Permission}
import silicon.utils.collections.mapReduceLeft

/* TODO: At least Term and Sort should go to the interfaces package.
 *       Maybe also Var and Literal.
 */
 
/* TODO: Sorts currently take not type parameters, will probably is necessary
 *       in order to support e.g. non-integer sequences.
 */
sealed trait Sort
object IntSort extends Sort { override val toString = "Int" }
object BoolSort extends Sort { override val toString = "Bool" }
object RefSort extends Sort { override val toString = "Ref" }

sealed trait Term {
	/* Attention! Do not use for non-term equalities, e.g. mu == waitlevel or
	 * seq1 == seq2.
	 */
	def ≡(t: Term): TermEq = TermEq(this, t)
	def ≠(t: Term): Term = Not(TermEq(this, t))
	
	/* Alternative:
	 *   1) Have one wrapper term FromTo(from: Sort, to: Sort)
	 *   2) Instantiate as needed
	 *   3) Decider collects all such terms before invoking the prover,
	 *      declares corresponding wrapper functions and wrapper axioms
	 *      before sending all terms to the prover.
	 *      BUT: Depending on the used TermConverter, some wrappers might be
	 *      unnecessary, e.g. when SeqSort is encoded as Int.
	 */
	def convert(from: Sort, to: Sort): Term = (from, to) match {
		case (IntSort, BoolSort) => IntToBool(this)
		case (BoolSort, IntSort) => BoolToInt(this)
		case (s1, s2) if s1 == s2 => this
		case (s1, s2) =>
			sys.error("Unexpected sort conversion %s -> %s.".format(from, to))
	}
	
	def convert(to: Sort): Term = convert(this.sort, to)
	
	def sort: Sort = IntSort /* Default sort */
	
	var srcNode: Option[SILASTNode] = None
	var srcPos: SILSourceLocation = SILNoLocation
	
	def setSrcNode(node: SILASTNode) = {
		this.srcNode = Some(node)
		if (this.srcPos == SILNoLocation) this.srcPos = node.sourceLocation

		this
	}
	
	def setSrcPos(pos: SILSourceLocation) = {
		this.srcPos = pos
		
		this
	}
	
	// def collect[R](f: Term => List[R]): List[R] = f(this)
}

/* TODO: Rename to Constant/Symbol/Id */
case class Var(id: String, override val sort: Sort) extends Term
	{ override val toString = id }
	
case class FApp(f: SILFunction, s: Term, t0: Term, tArgs: List[Term],
		override val sort: Sort) extends Term {
	
	// override def collect[R](f: Term => List[R]) =
		// f(this) ::: s.collect(f) ::: t0.collect(f) ::: (tArgs flatMap (t => t.collect(f)))
	
	override val toString =
		"FApp(%s, %s, %s, %s)".format(f.name, s, t0, tArgs.mkString(", "))
}

// case class Token[P <: Permission[P], H <: Heap[H]](m: ast.Method,
		// h: H, t0: Term, tArgs: List[Term]) extends Term {

	// override val toString =
		// "Token(%s, %s, %s)".format(h, t0, tArgs.mkString(", "))
// }

/* Literals */

sealed trait Literal extends Term

case object Unit extends Literal { override val toString = "_" }

case class IntLiteral(n: Int) extends Literal {
	def +(m: Int) = IntLiteral(n + m)
	def -(m: Int) = IntLiteral(n - m)	
	def *(m: Int) = IntLiteral(n * m)	
	def /(m: Int) = Div(this, IntLiteral(m))
	override val toString = n.toString
}

// object Null extends Literal {	override val toString = "Null" }
case class Null() extends Literal {	override val toString = "Null" }
// object MaxLock extends Literal { override val toString = "MLock" }
// object BottomLock extends Literal {	override val toString = "BLock" }
case class BottomLock() extends Literal {	override val toString = "BLock" }

// object True extends Literal {
case class True() extends Literal {
	override val sort = BoolSort
	override val toString = "True"
}

// object False extends Literal {
case class False() extends Literal {
	override val sort = BoolSort
	override val toString = "False"
}

/* Quantifiers */

sealed trait Quantifier extends Term { override val sort = BoolSort }

object Forall extends Quantifier { override val toString = "∀ " }
object Exists extends Quantifier { override val toString = "∃ " }

case class Quantification(q: Quantifier, tVars: List[Var], tBody: Term) 
		extends Term { override val sort = BoolSort }

/* Sequences */

sealed trait SeqTerm extends Term { /* override val sort: Sort = SeqSort */ }

case class SeqEq(p0: Term, p1: Term) extends Eq

case class RangeSeq(p0: Term, p1: Term) extends SeqTerm
		/* with BinaryOp[Term] */ {	/* override */ val op = ".." }

// object EmptySeq extends SeqTerm with Literal
case class EmptySeq() extends SeqTerm with Literal
	{ override val toString = "Nil" }

case class SeqElem(p: Term) extends SeqTerm /* with UnaryOp[Term] */
	{ override val toString = "(" + p + ")" }

case class SeqCon(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */
	{	/* override */ val op = "++" }

// case class SeqSeg(s: Term, i: Term, j: Term) extends SeqTerm
	// { override val toString = s + "[" + i + ".." + j + "]" }
	
case class SeqDrop(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
	override val sort = IntSort
	override val toString = p0 + "[" + p1 + ":]"
}

case class SeqTake(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
	override val sort = IntSort
	override val toString = p0 + "[:" + p1 + "]"
}

case class SeqLen(p: Term) extends SeqTerm /* with UnaryOp[Term] */ {
	override val sort = IntSort
	override val toString = "|" + p + "|"
}

case class SeqAt(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
	override val sort = IntSort /* TODO: Support non-int sequences */
	override val toString = p0 + "[" + p1 + "]"
}

case class SeqIn(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
	override val sort = BoolSort
	/* override */ val op = "in"
}

/* Monitors, locks */

sealed trait LockTerm extends Term { override val sort: Sort = BoolSort }

case class LockLess(p0: Term, p1: Term) extends LockTerm with ComparisonTerm
		/* with BinaryOp[Term] */ { /* override */ val op = "<<" }
    
// object MaxLock extends LockTerm { override val toString = "maxlock" }
case class MaxLock() extends LockTerm { override val toString = "maxlock" }

case class MaxLockLess(t: Term, hn: Int, mn: Int, cn: Int) extends LockTerm {
  val op = "<<"
  override val toString = "maxlock(%s, %s, %s) %s %s".format(hn, mn, cn, op, t)
}

/* TODO: If this should also be an Eq we have to remove BinaryOp from the
 *       declaration of Eq.
 */
case class MaxLockAtMost(t: Term, hn: Int, mn: Int, cn: Int) extends LockTerm {
  val op = "=="
  override val toString = "maxlock(%s, %s, %s) %s %s".format(hn, mn, cn, op, t)
}

sealed trait LockMode extends LockTerm

object LockMode {
	object Read extends LockMode { override def toString = "R" }
	object Write extends LockMode { override def toString = "W" }
	object None extends LockMode { override def toString = "N" }
}

case class Holds(t: Term, n: Int, p: LockMode) extends LockTerm
	{ override val toString = "holds(%s, %s, %s)".format(t, n, p) }

case class LockChange(which: List[Term], n1: Int, n2: Int)
		extends LockTerm {

  override val toString = "lockchange([%s], %s, %s)".format(
			which.mkString(", "), n1, n2)
}

case class Mu(p0: Term, n: Int, p1: Term) extends LockTerm
		/* with BinaryOp[Term] */ {

	override val sort = IntSort
	override val toString = "mu(%s, %s, %s)".format(p0, n, p1)
}

/* Credits */

case class Credits(t: Term, n: Int) extends Term
	{ override val toString = "credits(%s, %s)".format(t, n) }

case class DebtFreeExpr(n: Int) extends Term
	{ override val toString = "debtfree(%s)".format(n) }
	
/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term

case class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
		/* with commonnodes.Plus[Term] with commonnodes.StructuralEqualityBinOp[Term] */

// object Plus extends Function2[Term, Term, Term] {
	// val Zero = IntLiteral(0)
	
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (t0, Zero) => t0
		// case (Zero, t1) => t1
		// case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 + n1)
		// case _ => new Plus(e0, e1)
	// }
		
	// def unapply(t: Plus) = Some((t.p0, t.p1))
// }

case class Minus(val p0: Term, val p1: Term) extends ArithmeticTerm
		/* with commonnodes.Minus[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Minus extends Function2[Term, Term, Term] {
	// val Zero = IntLiteral(0)
	
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (t0, Zero) => t0
		// case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 - n1)
		// case (t0, t1) if t0 == t1 => Zero
		// case _ => new Minus(e0, e1)
	// }
		
	// def unapply(t: Minus) = Some((t.p0, t.p1))
// }

case class Times(val p0: Term, val p1: Term) extends ArithmeticTerm
		/* with commonnodes.Times[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Times extends Function2[Term, Term, Term] {
	// val Zero = IntLiteral(0)
	// val One = IntLiteral(1)

	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (t0, Zero) => Zero
		// case (Zero, t1) => Zero
		// case (t0, One) => t0
		// case (One, t1) => t1
		// case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 * n1)
		// case _ => new Times(e0, e1)
	// }
		
	// def unapply(t: Times) = Some((t.p0, t.p1))
// }

case class Div(p0: Term, p1: Term) extends ArithmeticTerm
		/* with commonnodes.Div[Term] */

case class Mod(p0: Term, p1: Term) extends ArithmeticTerm
		/* with commonnodes.Mod[Term] */

/* Boolean expression terms */		

sealed trait BooleanTerm extends Term { override val sort = BoolSort }

case class Not(val p: Term) extends BooleanTerm /* with commonnodes.Not[Term] {
	override val op = "¬"
	
	override val toString = p match {
		case eq: Eq => eq.p0.toString + "≠" + eq.p1.toString
		case _ => super.toString
	}
	
	override def equals(other: Any) =
		this.eq(other.asInstanceOf[AnyRef]) || (other match {
			case Not(_p) => p == _p
			case _ => false
		})
}
*/

// object Not {
	// def apply(e0: Term) = e0 match {
		// case Not(e1) => e1
		// case True() => False()
		// case False() => True()
		// case _ => new Not(e0)
	// }
	
	// def unapply(e: Not) = Some((e.p))
// }

case class Or(val p0: Term, val p1: Term) extends BooleanTerm
		/* with commonnodes.Or[Term] with commonnodes.StructuralEqualityBinOp[Term] */

// object Or extends Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (True(), _) | (_, True()) => True()
		// case (False(), e1) => e1
		// case (e0, False()) => e0
		// case (e0, e1) if e0 == e1 => e0
		// case _ => new Or(e0, e1)
	// }
	
	// def unapply(e: Or) = Some((e.p0, e.p1))
// }

case class And(val p0: Term, val p1: Term) extends BooleanTerm
		/* with commonnodes.And[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object And extends Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (True(), e1) => e1
		// case (e0, True()) => e0
		// case (False(), _) | (_, False()) => False()
		// case (e0, e1) if e0 == e1 => e0
		// case _ => new And(e0, e1)
	// }
	
	// def unapply(e: And) = Some((e.p0, e.p1))
// }
		
case class Implies(val p0: Term, val p1: Term) extends BooleanTerm
		/* with commonnodes.Implies[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Implies extends Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term): Term = (e0, e1) match {
		// case (True(), e1) => e1
		// case (e0, True()) => True()
		// case (e0, Implies(e10, e11)) => Implies(And(e0, e10), e11)
		// case (False(), _) => True()
		// case (e0, e1) if e0 == e1 => True()
		// case _ => new Implies(e0, e1)
	// }
	
	// def unapply(e: Implies) = Some((e.p0, e.p1))
// }

case class Iff(val p0: Term, val p1: Term) extends BooleanTerm
		/* with commonnodes.Iff[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Iff extends Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (True(), e1) => e1
		// case (e0, True()) => e0
		// case (e0, e1) if e0 == e1 => e0
		// case _ => new Iff(e0, e1)
	// }

	// def unapply(e: Iff) = Some((e.p0, e.p1))
// }

case class Ite(val t0: Term, val t1: Term, val t2: Term) extends BooleanTerm {
	assert(t0.sort == BoolSort && t1.sort == t2.sort, /* @elidable */
			"Ite term Ite(%s, %s, %s) is not well-sorted: %s, %s, %s"
			.format(t0, t1, t2, t0.sort, t1.sort, t2.sort))

	override val toString = "Ite(%s, %s, %s)".format(t0, t1, t2)
	
	override def equals(other: Any) =
		this.eq(other.asInstanceOf[AnyRef]) || (other match {
			case Ite(_t0, _t1, _t2) => t0 == _t0 && t1 == _t1 && t2 == _t2
			case _ => false
		})
}

// object Ite extends Function3[Term, Term, Term, Term] {
	// def apply(e0: Term, e1: Term, e2: Term) = e0 match {
		// case True() => e1
		// case False() => e2
		// case _ => new Ite(e0, e1, e2)
	// }
	
	// def unapply(e: Ite) = Some((e.t0, e.t1, e.t2))	
// }

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

/* TODO: Make more specific by using a generic T <: Term, so that e.g. equality
 *       on sequences can range over SeqTerms.
 */
sealed trait Eq extends ComparisonTerm /* with commonnodes.Eq[Term] */ {
	def p0: Term
	def p1: Term
}

case class TermEq(p0: Term, p1: Term) extends Eq

case class Less(val p0: Term, val p1: Term) extends ComparisonTerm
		/* with commonnodes.Less[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Less extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True() else False()
		// case (t0, t1) if t0 == t1 => False()
		// case _ => new Less(e0, e1)
	// }
	
	// def unapply(e: Less) = Some((e.p0, e.p1))
// }
		
case class AtMost(val p0: Term, val p1: Term) extends ComparisonTerm
		/* with commonnodes.AtMost[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object AtMost extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True() else False()
		// case (t0, t1) if t0 == t1 => True()
		// case _ => new AtMost(e0, e1)
	// }
	
	// def unapply(e: AtMost) = Some((e.p0, e.p1))
// }

case class Greater(val p0: Term, val p1: Term) extends ComparisonTerm
		/* with commonnodes.Greater[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Greater extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True() else False()
		// case (t0, t1) if t0 == t1 => False()
		// case _ => new Greater(e0, e1)
	// }
	
	// def unapply(e: Greater) = Some((e.p0, e.p1))
// }

case class AtLeast(val p0: Term, val p1: Term) extends ComparisonTerm
		/* with commonnodes.AtLeast[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True() else False()
		// case (t0, t1) if t0 == t1 => True()
		// case _ => new AtLeast(e0, e1)
	// }
	
	// def unapply(e: AtLeast) = Some((e.p0, e.p1))
// }
		
/* Auxiliary terms */
	
case class Combine(t0: Term, t1: Term) extends Term

case class SnapEq(p0: Term, p1: Term) extends Eq

sealed trait SortWrapper extends Term { def t0: Term }

case class BoolToInt(t0: Term) extends SortWrapper
case class IntToBool(t0: Term) extends SortWrapper
	{ override val sort = BoolSort }
	
case class UpdateMap(id: String, t: Term, n: Int) extends LockTerm
	{ override val toString = "%s[%s,%s]".format(id, t, n) }

/* Utility functions */
		
object utils {
	def ¬(t: Term) = Not(t)
	
	def SetAnd(it: Iterable[Term], f: Term => Term = t => t) =
		mapReduceLeft(it, f, And, True())

	def SetOr(it: Iterable[Term], f: Term => Term = t => t): Term =
		mapReduceLeft(it, f, Or, True())
}