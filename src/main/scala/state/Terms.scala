package semper
package silicon
package state.terms

import ast.commonnodes
import ast.commonnodes.{BinaryOp}
import interfaces.state.{Heap}
import silicon.utils.collections.mapReduceLeft

/* Why not have a Term[S <: Sort]?
 * Then we cannot have optimising extractor objects anymore, because these
 * don't take type parameters. However, defining a DSL seems to only be
 * possible when Term can be parameterised ...
 * Hm, reusing e.g. Times for Ints and Perms seems to be problematic w.r.t.
 * to optimising extractor objects because the optimisations depend on the
 * sort, e.g. IntLiteral(a) * IntLiteral(b) ~~> IntLiteral(a * b),
 *            Perms(t) * FullPerms() ~~> Perms(t)
 * It would be better if we could specify dsl.Operand for different
 * Term[Sorts], along with the optimisations. Maybe some type level
 * programming can be used to have an implicit that applies the
 * optimisations, as done in the work on the type safe builder pattern.
 */

/* TODO: Sorts currently take not type parameters, will probably is necessary
 *       in order to support e.g. non-integer sequences.
 */

/* TODO: Can we use scala.FunctionN instead of UnaryOperator, BinaryOperator?
 *
 */

sealed trait Sort /*{
  def sortParameters: Seq[Sort] = Nil
}*/

object sorts {
  object Snap extends Sort { override val toString = "Snap" }
  object Int extends Sort { override val toString = "Int" }
  object Bool extends Sort { override val toString = "Bool" }
  object Ref extends Sort { override val toString = "Ref" }
  object Perms extends Sort { override val toString = "Perms" }
//  object LockMode extends Sort { override val toString = "LockMode" }
//  object Mu extends Sort { override val toString = "Mu" }
//
//  case class Seq(val elementsSort: Sort) extends Sort {
//    override val sortParameters = elementsSort :: Nil
//    override val toString = "Seq[%s]".format(elementsSort)
//  }
case class UserSort(id: String) extends Sort {
  override val toString = id
}
}

sealed trait Term {
	/* Attention! Do not use for non-term equalities, e.g. mu == waitlevel or
	 * seq1 == seq2.
	 */
	def ===(t: Term): TermEq = TermEq(this, t)
	def !==(t: Term): Term = Not(TermEq(this, t))

	def convert(to: Sort): Term = this match {
    case _ if to == this.sort => this
    case sw: SortWrapper if sw.t.sort == to => sw.t
    case _ => SortWrapper(this, to)
  }

	def sort: Sort
	
	var srcNode: Option[ast.ASTNode] = None
	var srcLoc: ast.SourceLocation = ast.NoLocation
	
	def setSrcNode(node: ast.ASTNode) = {
		this.srcNode = Some(node)
		if (this.srcLoc == ast.NoLocation) this.srcLoc = node.sourceLocation

		this
	}
	
	def setSrcLoc(loc: ast.SourceLocation) = {
		this.srcLoc = loc
		
		this
	}
}

/* TODO: Rename to Constant/Symbol/Id */
case class Var(id: String, override val sort: Sort) extends Term
	{ override val toString = id }

case class FApp(val f: semper.sil.ast.programs.symbols.Function,
                val s: Term,
                val t0: Term,
                val tArgs: Seq[Term],
                val sort: Sort)
    extends Term {

  utils.assertSort(s, "snapshot", sorts.Snap)

  override val toString = "FApp(%s, %s, %s, %s)".format(f.name, s, t0, tArgs.mkString(", "))
}

//case class Token[H <: Heap[H]](m: ast.Implementation, h: H, rdVar: Var, t0: Term, tArgs: List[Term])
//    extends Term {
//
//  utils.assertSort(rdVar, "var", sorts.Perms)
//
//  val sort = sorts.Ref
//
//	override val toString =
//		"Token(%s, %s, %s, %s)".format(h, rdVar, t0, tArgs.mkString(", "))
//}

sealed trait ReferenceTerm extends Term { val sort = sorts.Ref }

//sealed trait MuTerm extends Term { val sort = sorts.Mu }

/* Literals */

sealed trait Literal extends Term

case object Unit extends SnapshotTerm with Literal {
  override val toString = "_"
}

case class IntLiteral(n: Int) extends ArithmeticTerm with Literal {
	def +(m: Int) = IntLiteral(n + m)
	def -(m: Int) = IntLiteral(n - m)	
	def *(m: Int) = IntLiteral(n * m)	
	def /(m: Int) = Div(this, IntLiteral(m))
	override val toString = n.toString
}

// object Null extends Literal {	override val toString = "Null" }
case class Null() extends ReferenceTerm with Literal {
  override val toString = "Null"
}
// object MaxLock extends Literal { override val toString = "MLock" }
// object BottomLock extends Literal {	override val toString = "BLock" }
//case class BottomLock() extends MuTerm with Literal {
//  override val toString = "BLock"
//}

//case class InitialMu() extends MuTerm with Literal {
//  override val toString = "IMu"
//}

sealed trait BooleanLiteral extends BooleanTerm with Literal {
  def value: Boolean
  override def toString = value.toString
}

case class True() extends BooleanLiteral {
  val value = true
	override val toString = "True"
}

case class False() extends BooleanLiteral {
  val value = false
  override val toString = "False"
}

/* Quantifiers */

sealed trait Quantifier

object Forall extends Quantifier { override val toString = "∀ " }
object Exists extends Quantifier { override val toString = "∃ " }

case class Quantification(q: Quantifier, qvar: Var, tBody: Term) extends BooleanTerm

///* Sequences */
//
//sealed trait SeqTerm extends Term {
//  val elementsSort: Sort
//  val sort: sorts.Seq
//}
//
//case class SeqEq(p0: Term, p1: Term) extends Eq {
//  utils.assertSameSeqSorts(p0, p1)
//
//  val elementsSort = p0.sort.sortParameters.head
//}
//
//case class RangeSeq(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
//  utils.assertSort(p0, "first operand", sorts.Int)
//  utils.assertSort(p1, "second operand", sorts.Int)
//
////  utils.assertValidBinSeqOpSort(p0, p1)
////  println("\n[RangeSeq]")
////  println("  p0 = " + p0)
////  println("  p0.sort = " + p0.sort)
////  println("  p1 = " + p1)
////  println("  p1.sort = " + p1.sort)
//
//  val elementsSort = sorts.Int
//  val sort = sorts.Seq(elementsSort)
//
//  override val toString = "[%s..%s]".format(p0, p1)
//}
//
//// object EmptySeq extends SeqTerm with Literal
//case class EmptySeq(elementsSort: Sort) extends SeqTerm with Literal {
//  val sort = sorts.Seq(elementsSort)
//  override val toString = "Nil"
//}
//
//case class SeqElem(p: Term) extends SeqTerm /* with UnaryOp[Term] */ {
////  utils.assertSort(p, "term", "Seq", _.isInstanceOf[sorts.Seq])
////  println("[SeqElem]")
////  println("  p = " + p)
////  println("  p.sort = " + p.sort)
//
//  val elementsSort = p.sort //.sortParameters.head
//  val sort = sorts.Seq(elementsSort)
////  println("  this.sort = " + this.sort)
////  println()
//  override val toString = "[" + p + "]"
//}
//
//case class SeqCon(p0: Term, p1: Term) extends SeqTerm with BinaryOp[Term] {
//  utils.assertSameSeqSorts(p0, p1)
//
//  val elementsSort = p0.sort.sortParameters.head
//  val sort = sorts.Seq(elementsSort)
//
//  override val op = "++"
//}
//
//case class SeqDrop(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
//  utils.assertSort(p0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
//  utils.assertSort(p1, "second operand", sorts.Int)
////  utils.assertSameSeqSorts(p0, p1)
//
//  val elementsSort = p0.sort.sortParameters.head
//  val sort = sorts.Seq(elementsSort)
//
//	override val toString = p0 + "[" + p1 + ":]"
//}
//
//case class SeqTake(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
//  utils.assertSort(p0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
//  utils.assertSort(p1, "second operand", sorts.Int)
//
//  val elementsSort = p0.sort.sortParameters.head
//  val sort = sorts.Seq(elementsSort)
//
//	override val toString = p0 + "[:" + p1 + "]"
//}
//
//case class SeqLen(p: Term) extends Term /* with UnaryOp[Term] */ {
//  utils.assertSort(p, "term", "Seq", _.isInstanceOf[sorts.Seq])
//
//  val sort = sorts.Int
//	override val toString = "|" + p + "|"
//}
//
//case class SeqAt(p0: Term, p1: Term) extends Term /* with BinaryOp[Term] */ {
//  utils.assertSort(p0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
//  utils.assertSort(p1, "second operand", sorts.Int)
//
////  val elementsSort = p0.sort.sortParameters.head
////  val sort = sorts.Seq(elementsSort)
//  val sort = p0.sort.sortParameters.head
//
//	override val toString = p0 + "[" + p1 + "]"
//}
//
//case class SeqIn(p0: Term, p1: Term) extends BooleanTerm /* with BinaryOp[Term] */ {
//  utils.assertSort(p0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
//  utils.assertSort(p1, "second operand", p0.sort.sortParameters.head)
//
//	override val toString = "%s in %s".format(p1, p0)
//}
//
///* Monitors, locks */
//
//case class LockLess(p0: Term, p1: Term) extends ComparisonTerm with BinaryOp[Term] {
//  utils.assertSort(p0, "first operand", sorts.Mu)
//  utils.assertSort(p1, "second operand", sorts.Mu)
//
//  override val op = "<<"
//}

// object MaxLock extends LockTerm { override val toString = "maxlock" }
//case class MaxLock() extends MuTerm { override val toString = "maxlock" }

//case class MaxLockLess(t: Term, hn: Int, mn: Int, cn: Int) extends ComparisonTerm {
//  val op = "<<"
//  override val toString = "maxlock(%s, %s, %s) %s %s".format(hn, mn, cn, op, t)
//}
//case class MaxLockLess(others: Iterable[Term], rcvr: Term, mu: Term) extends ComparisonTerm {
//  others.foreach(o => utils.assertSort(o, "first operand", sorts.Mu))
//  utils.assertSort(rcvr, "second operand", sorts.Ref)
//  utils.assertSort(mu, "third operand", sorts.Mu)
//
//  val op = "<<"
//  override lazy val toString = "%s %s %s (rcvr = %s)".format(others.mkString(","), op, mu, rcvr)
//}
//
////case class MaxLockAtMost(t: Term, hn: Int, mn: Int, cn: Int) extends ComparisonTerm {
////  val op = "=="
////  override val toString = "maxlock(%s, %s, %s) %s %s".format(hn, mn, cn, op, t)
////}
//case class MaxLockAtMost(others: Iterable[Term], rcvr: Term, mu: Term) extends ComparisonTerm {
//  others.foreach(o => utils.assertSort(o, "first operand", sorts.Mu))
//  utils.assertSort(rcvr, "second operand", sorts.Ref)
//  utils.assertSort(mu, "third operand", sorts.Mu)
//
//  val op = "=="
//  override lazy val toString = "%s %s %s (rcvr = %s)".format(others.mkString(","), op, mu, rcvr)
//}

//sealed trait LockModeTerm extends Term { override def sort = sorts.LockMode }
//
//object LockMode {
//	case class Read() extends LockModeTerm with Literal { override def toString = "R" }
//  case class Write() extends LockModeTerm with Literal  { override def toString = "W" }
//  case class None() extends LockModeTerm with Literal  { override def toString = "N" }
//}

//case class InitialHolds(rcvr: Term) extends LockModeTerm
//  { override def toString = "holds0(%s)".format(rcvr) }
//
//case class InitialMu(rcvr: Term) extends MuTerm
//  { override def toString = "mu0(%s)".format(rcvr) }

//case class InitialCredits(rcvr: Term) extends Term {
//  utils.assertSort(rcvr, "receiver", sorts.Ref)
//
//  override val sort = sorts.Int
//  override def toString = "mu0(%s)".format(rcvr)
//}

//case class Holds(t: Term, n: Int, lm: LockModeTerm) extends BooleanTerm
//	{ override val toString = "holds(%s, %s, %s)".format(t, n, lm) }

//case class Holds(rcvr: Term, mode: Term) extends LockModeTerm {
//  utils.assertSort(mode, "second operand", sorts.LockMode)
//  override val toString = "holds(%s, %s)".format(rcvr, mode)
//}

//case class LockChange(which: List[Term], n1: Int, n2: Int) extends BooleanTerm {
//  override val toString = "lockchange([%s], %s, %s)".format(which.mkString(", "), n1, n2)
//}

//case class Mu(p0: Term, n: Int, p1: Term) extends MuTerm with BinaryOp[Term] {
//  utils.assertSort(p1, "argument p1 (mu-value)", sorts.Int)
//
//	override val toString = "mu(%s, %s, %s)".format(p0, n, p1)
//}

///* Credits */
//
//case class Credits(t: Term, n: Int) extends Term {
//  val sort = sorts.Int
//  override val toString = "credits(%s, %s)".format(t, n)
//}
//
//case class DebtFreeExpr(n: Int) extends BooleanTerm
//	{ override val toString = "debtfree(%s)".format(n) }
	
/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
		with commonnodes.Plus[Term] with commonnodes.StructuralEqualityBinOp[Term]

object Plus extends Function2[Term, Term, Term] {
	val Zero = IntLiteral(0)
	
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (t0, Zero) => t0
		case (Zero, t1) => t1
		case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 + n1)
		case _ => new Plus(e0, e1)
	}
		
	def unapply(t: Plus) = Some((t.p0, t.p1))
}

class Minus(val p0: Term, val p1: Term) extends ArithmeticTerm
		with commonnodes.Minus[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Minus extends Function2[Term, Term, Term] {
	val Zero = IntLiteral(0)
	
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (t0, Zero) => t0
		case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 - n1)
		case (t0, t1) if t0 == t1 => Zero
		case _ => new Minus(e0, e1)
	}
		
	def unapply(t: Minus) = Some((t.p0, t.p1))
}

class Times(val p0: Term, val p1: Term) extends ArithmeticTerm
		with commonnodes.Times[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Times extends Function2[Term, Term, Term] {
	val Zero = IntLiteral(0)
	val One = IntLiteral(1)

	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (t0, Zero) => Zero
		case (Zero, t1) => Zero
		case (t0, One) => t0
		case (One, t1) => t1
		case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 * n1)
		case _ => new Times(e0, e1)
	}
		
	def unapply(t: Times) = Some((t.p0, t.p1))
}

case class Div(p0: Term, p1: Term) extends ArithmeticTerm
		with commonnodes.Div[Term]

case class Mod(p0: Term, p1: Term) extends ArithmeticTerm
		with commonnodes.Mod[Term]

/* Boolean expression terms */		

sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }

class Not(val p: Term) extends BooleanTerm with commonnodes.Not[Term] {
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

object Not {
	def apply(e0: Term) = e0 match {
		case Not(e1) => e1
		case True() => False()
		case False() => True()
		case _ => new Not(e0)
	}
	
	def unapply(e: Not) = Some((e.p))
}

class Or(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Or[Term] with commonnodes.StructuralEqualityBinOp[Term]

/* TODO: Or should be (Term, Term) => BooleanTerm, but that require a
 *       Boolean(t: Term) wrapper, because e0/e1 may just be a Var.
 *       It would be sooooo handy to be able to work with Term[Sort], but
 *       that conflicts with using extractor objects to simplify terms,
 *       since extractor objects can't be type-parameterised.
 */
object Or extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (True(), _) | (_, True()) => True()
		case (False(), e1) => e1
		case (e0, False()) => e0
		case (e0, e1) if e0 == e1 => e0
		case _ => new Or(e0, e1)
	}
	
	def unapply(e: Or) = Some((e.p0, e.p1))
}

class And(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.And[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object And extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (True(), e1) => e1
		case (e0, True()) => e0
		case (False(), _) | (_, False()) => False()
		case (e0, e1) if e0 == e1 => e0
		case _ => new And(e0, e1)
	}
	
	def unapply(e: And) = Some((e.p0, e.p1))
}
		
class Implies(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Implies[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Implies extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term): Term = (e0, e1) match {
		case (True(), e1) => e1
		case (False(), _) => True()
		case (e0, True()) => True()
		case (e0, Implies(e10, e11)) => Implies(And(e0, e10), e11)
		case (e0, e1) if e0 == e1 => True()
		case _ => new Implies(e0, e1)
	}
	
	def unapply(e: Implies) = Some((e.p0, e.p1))
}

class Iff(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Iff[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Iff extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (True(), e1) => e1
		case (e0, True()) => e0
		case (e0, e1) if e0 == e1 => True()
		case _ => new Iff(e0, e1)
	}

	def unapply(e: Iff) = Some((e.p0, e.p1))
}

class Ite(val t0: Term, val t1: Term, val t2: Term) extends Term {
	assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
			"Ite term Ite(%s, %s, %s) is not well-sorted: %s, %s, %s"
			.format(t0, t1, t2, t0.sort, t1.sort, t2.sort))

	override val toString = "Ite(%s, %s, %s)".format(t0, t1, t2)
	
	override def equals(other: Any) =
		this.eq(other.asInstanceOf[AnyRef]) || (other match {
			case Ite(_t0, _t1, _t2) => t0 == _t0 && t1 == _t1 && t2 == _t2
			case _ => false
		})
    
  override val sort = t1.sort
}

object Ite extends Function3[Term, Term, Term, Term] {
	def apply(e0: Term, e1: Term, e2: Term) = e0 match {
		case True() => e1
		case False() => e2
		case _ => new Ite(e0, e1, e2)
	}
	
	def unapply(e: Ite) = Some((e.t0, e.t1, e.t2))	
}

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

/* TODO: Make more specific by using a generic T <: Term, so that e.g. equality
 *       on sequences can range over SeqTerms.
 */
sealed trait Eq extends ComparisonTerm with commonnodes.Eq[Term] {
  assert(p0.sort == p1.sort,
         ("Expected both operands to be of the same sort, but found %s (%s) " +
          "and %s (%s).").format(p0.sort, p0, p1.sort, p1))
}

case class TermEq(p0: Term, p1: Term) extends Eq

class Less(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.Less[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Less extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True() else False()
		case (t0, t1) if t0 == t1 => False()
		case _ => new Less(e0, e1)
	}
	
	def unapply(e: Less) = Some((e.p0, e.p1))
}
		
class AtMost(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.AtMost[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object AtMost extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True() else False()
		case (t0, t1) if t0 == t1 => True()
		case _ => new AtMost(e0, e1)
	}
	
	def unapply(e: AtMost) = Some((e.p0, e.p1))
}

class Greater(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.Greater[Term] with commonnodes.StructuralEqualityBinOp[Term]
		
object Greater extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True() else False()
		case (t0, t1) if t0 == t1 => False()
		case _ => new Greater(e0, e1)
	}
	
	def unapply(e: Greater) = Some((e.p0, e.p1))
}

class AtLeast(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.AtLeast[Term] with commonnodes.StructuralEqualityBinOp[Term]

object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True() else False()
		case (t0, t1) if t0 == t1 => True()
		case _ => new AtLeast(e0, e1)
	}

	def unapply(e: AtLeast) = Some((e.p0, e.p1))
}

/*
 * Permissions
 */

//sealed trait PermissionsTerm extends Term

sealed trait PotentiallyWriteStatus

object PotentiallyWriteStatus {
  case object True extends PotentiallyWriteStatus
  case object False extends PotentiallyWriteStatus
  case object Unknown extends PotentiallyWriteStatus
}

sealed trait PermissionsTerm[P <: PermissionsTerm[P]] extends Term {
  override val sort = sorts.Perms

  def +(other: P): P
  def -(other: P): P
  def *(other: P): P
  def <(other: P): BooleanTerm
  def >(other: P): BooleanTerm

  def isPotentiallyWrite: PotentiallyWriteStatus
}

class PermissionsTuple(val w: FractionalPermissions, val r: FractionalPermissions)
    extends PermissionsTerm[PermissionsTuple] {

  val combined = w + r
  override val isPotentiallyWrite = w.isPotentiallyWrite

  def +(other: PermissionsTuple) = PermissionsTuple(this.w + other.w, this.r + other.r)
  def -(other: PermissionsTuple) = PermissionsTuple(this.w - other.w, this.r - other.r)

  def *(other: PermissionsTuple) =
      PermissionsTuple(this.w * other.w,
                      (this.w * other.r) + (this.r * other.w) + (this.r * other.r))

  def <(other: PermissionsTuple) = this.combined < other.combined
  def >(other: PermissionsTuple) = this.combined > other.combined

  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case pt: PermissionsTuple if pt.getClass.eq(this.getClass) => w == pt.w && r == pt.r
      case _ => false
    })

  override def hashCode(): Int = w.hashCode() * r.hashCode()

  override val toString = "(%s, %s)".format(w, r)
}

object PermissionsTuple extends ((FractionalPermissions, FractionalPermissions) => PermissionsTuple) {
  def apply(w: FractionalPermissions, r: FractionalPermissions): PermissionsTuple =
    new PermissionsTuple(w, r)

  def apply(fp: FractionalPermissions): PermissionsTuple = fp match {
    case _: PotentiallyWriteFractionalPermissions => PermissionsTuple(fp, ZeroPerms())
    case _: NonPotentiallyWriteFractionalPermissions => PermissionsTuple(ZeroPerms(), fp)

    case PermPlus(fp1, fp2) => PermissionsTuple(fp1) + PermissionsTuple(fp2)
    case PermMinus(fp1, fp2) => PermissionsTuple(fp1) - PermissionsTuple(fp2)
    case PermTimes(fp1, fp2) => PermissionsTuple(fp1) * PermissionsTuple(fp2)

    case IntPermTimes(t1, fp1) =>
      val pt = PermissionsTuple(fp1)
      new PermissionsTuple(IntPermTimes(t1, pt.w), IntPermTimes(t1, pt.r))

    case _ =>
      sys.error("Not yet implemented for %s (%s)".format(fp, fp.getClass.getSimpleName))
  }

//  def apply(fp: FractionalPermissions): PermissionsTuple = fp.isPotentiallyWrite match {
//    case PotentiallyWriteStatus.True => PermissionsTuple(fp, ZeroPerms())
//    case PotentiallyWriteStatus.False => PermissionsTuple(ZeroPerms(), fp)
//
//    case PotentiallyWriteStatus.Unknown =>
//      sys.error("Not yet implemented for %s (%s)".format(fp, fp.getClass.getSimpleName))
//  }

//  def apply(fp: FractionalPermissions): PermissionsTuple = fp match {
//    case _: AtomicPotentiallyWritePermissionsTerm => PermissionsTuple(fp, ZeroPerms())
//    case _: AtomicReadPermissionsTerm => PermissionsTuple(ZeroPerms(), fp)
//
//    case _: CompoundPermissionsTerm =>
//      sys.error("Not yet implemented for %s (%s)".format(fp, fp.getClass.getSimpleName))
//  }

  def unapply(pt: PermissionsTuple) = Some((pt.w, pt.r))
}

sealed trait FractionalPermissions extends PermissionsTerm[FractionalPermissions] {
  def +(other: FractionalPermissions) = PermPlus(this, other)
  def -(other: FractionalPermissions) = PermMinus(this, other)
  def *(other: FractionalPermissions) = PermTimes(this, other)
  def <(other: FractionalPermissions) = PermLess(this, other)
  def >(other: FractionalPermissions) = PermLess(other, this)
}

sealed trait NonPotentiallyWriteFractionalPermissions extends FractionalPermissions {
  val isPotentiallyWrite = PotentiallyWriteStatus.False
}

sealed trait PotentiallyWriteFractionalPermissions extends FractionalPermissions  {
  val isPotentiallyWrite = PotentiallyWriteStatus.True
}

sealed trait FractionalPermissionsExpression extends FractionalPermissions  {
  val isPotentiallyWrite: PotentiallyWriteStatus = PotentiallyWriteStatus.Unknown
}

case class FullPerms() extends PotentiallyWriteFractionalPermissions { override val toString = "W" }
case class PercPerms(n: Int) extends PotentiallyWriteFractionalPermissions { override val toString = n + "%" }

case class ZeroPerms() extends NonPotentiallyWriteFractionalPermissions { override val toString = "Z" }
case class ReadPerms(v: Var) extends NonPotentiallyWriteFractionalPermissions { override val toString = v.toString }
case class InternalRdPerms() extends NonPotentiallyWriteFractionalPermissions { override val toString = "iRd" }
case class MonitorRdPerms() extends NonPotentiallyWriteFractionalPermissions { override val toString = "mRd" }
case class PredicateRdPerms() extends NonPotentiallyWriteFractionalPermissions { override val toString = "pRd" }
case class ChannelRdPerms() extends NonPotentiallyWriteFractionalPermissions { override val toString = "cRd" }
case class StarPerms(v: Var) extends NonPotentiallyWriteFractionalPermissions { override val toString = v.toString }

case class TermPerms(val t: Term) extends NonPotentiallyWriteFractionalPermissions {
  utils.assertSort(t, "term", sorts.Perms)

  override val toString = "Perms(%s)".format(t)
}

case class IsValidPerms(v: Var, ub: FractionalPermissions) extends BooleanTerm {
  override val toString = "PVar(%s, %s)".format(v.toString, ub)
}

case class IsReadPerms(v: Var, ub: FractionalPermissions) extends BooleanTerm {
  override val toString = "RdVar(%s, %s)".format(v.toString, ub)
}

/* case */ class PermTimes(val p0: FractionalPermissions, val p1: FractionalPermissions)
    extends FractionalPermissionsExpression
    with commonnodes.Times[FractionalPermissions]
    with commonnodes.StructuralEqualityBinOp[FractionalPermissions]

object PermTimes extends ((FractionalPermissions, FractionalPermissions) => FractionalPermissions) {
  def apply(t0: FractionalPermissions, t1: FractionalPermissions) = (t0, t1) match {
    case (FullPerms(), t) => t
    case (t, FullPerms()) => t
    case (ZeroPerms(), _) => ZeroPerms()
    case (_, ZeroPerms()) => ZeroPerms()
//    case (PercPerms(n), PercPerms(m)) => PercPerms(n * m)
    case (_, _) => new PermTimes(t0, t1)
  }
  
  def unapply(pt: PermTimes) = Some((pt.p0, pt.p1))
}

class IntPermTimes(val p0: Term, val p1: FractionalPermissions)
    extends FractionalPermissionsExpression
    with commonnodes.Times[Term]
    with commonnodes.StructuralEqualityBinOp[Term] {

  override val isPotentiallyWrite = p1.isPotentiallyWrite
}

object IntPermTimes extends ((Term, FractionalPermissions) => FractionalPermissions) {
  def apply(t0: Term, t1: FractionalPermissions) = (t0, t1) match {
    case (IntLiteral(1), t) => t
    case (_, ZeroPerms()) => ZeroPerms()
    //    case (PercPerms(n), PercPerms(m)) => PercPerms(n * m)
    case (_, _) => new IntPermTimes(t0, t1)
  }

  def unapply(pt: IntPermTimes) = Some((pt.p0, pt.p1))
}

/* case */ class PermPlus(val p0: FractionalPermissions, val p1: FractionalPermissions)
    extends FractionalPermissionsExpression
    with commonnodes.Plus[FractionalPermissions]
    with commonnodes.StructuralEqualityBinOp[FractionalPermissions]

object PermPlus extends ((FractionalPermissions, FractionalPermissions) => FractionalPermissions) {
  def apply(t0: FractionalPermissions, t1: FractionalPermissions) = (t0, t1) match {
    case (ZeroPerms(), _) => t1
    case (_, ZeroPerms()) => t0
    case (PercPerms(n), PercPerms(m)) => if (n == -m) ZeroPerms() else PercPerms(n + m)
    case (_, _) => new PermPlus(t0, t1)
  }
  
  def unapply(pp: PermPlus) = Some((pp.p0, pp.p1))
}

/* case */ class PermMinus(val p0: FractionalPermissions, val p1: FractionalPermissions)
    extends FractionalPermissionsExpression
    with commonnodes.Minus[FractionalPermissions]
    with commonnodes.StructuralEqualityBinOp[FractionalPermissions]

object PermMinus extends ((FractionalPermissions, FractionalPermissions) => FractionalPermissions) {
  def apply(t0: FractionalPermissions, t1: FractionalPermissions) = (t0, t1) match {
    case (_, ZeroPerms()) => t0
    case (p0, p1) if p0 == p1 => ZeroPerms()
    case (PercPerms(n), PercPerms(m)) => if (n == m) ZeroPerms() else PercPerms(n - m)
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => new PermMinus(t0, t1)
  }
  
  def unapply(pm: PermMinus) = Some((pm.p0, pm.p1))
}

/* case */ class PermLess(val p0: FractionalPermissions, val p1: FractionalPermissions)
    extends BooleanTerm
    with commonnodes.Less[FractionalPermissions]
    with commonnodes.StructuralEqualityBinOp[FractionalPermissions] {

  override val toString = "%s < %s".format(p0, p1)
}

object PermLess extends ((FractionalPermissions, FractionalPermissions) => BooleanTerm) {
  def apply(t0: FractionalPermissions, t1: FractionalPermissions) = (t0, t1) match {
    case (t0, t1) if t0 == t1 => False()
    case (_, _) => new PermLess(t0, t1)
  }
  
  def unapply(pl: PermLess) = Some((pl.p0, pl.p1))
}

///* Immutability */
//
//sealed trait ImmutabilityTerm extends BooleanTerm
//
//case class Immutable(t: Term, id: String) extends ImmutabilityTerm
//case class Frozen(t: Term, id: String) extends ImmutabilityTerm

/* Domains */

case class DomainFApp(val id: String, val tArgs: Seq[Term], val sort: Sort) extends Term {
  override val toString = id + tArgs.mkString("(", ", ", ")")
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

case class SnapEq(p0: Term, p1: Term) extends Eq {
  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)
}

case class Combine(t0: Term, t1: Term) extends SnapshotTerm {
  utils.assertSort(t0, "first operand", sorts.Snap)
  utils.assertSort(t1, "second operand", sorts.Snap)
}

case class First(t: Term) extends SnapshotTerm {
  utils.assertSort(t, "term", sorts.Snap)
}

case class Second(t: Term) extends SnapshotTerm {
  utils.assertSort(t, "term", sorts.Snap)
}

case class SortWrapper(t: Term, to: Sort) extends Term {
  assert(!(t.sort == sorts.Ref && to == sorts.Int),
         "Unexpected sort wrapping from %s to %s".format(t.sort, to))

  override val toString = "(%s) %s".format(to, t)
  override val sort = to
}

/* Auxiliary terms */

//case class UpdateMap(id: String, t: Term, n: Int) extends BooleanTerm
//	{ override val toString = "%s[%s,%s]".format(id, t, n) }

case class TypeOf(t: Term, typeName: String) extends BooleanTerm {
  utils.assertSort(t, "term", sorts.Ref)

  override val toString = "%s == %s".format(t, typeName)
}

/* Utility functions */

object utils {
  def ¬(t: Term) = Not(t)

  def BigAnd(it: Iterable[Term], f: Term => Term = t => t) =
    mapReduceLeft(it, f, And, True())

  def BigOr(it: Iterable[Term], f: Term => Term = t => t): Term =
    mapReduceLeft(it, f, Or, True())

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, s: Sort) {
    assert(t.sort == s,
           "Expected %s %s to be of sort %s, but found %s.".format(desc, t, s, t.sort))
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, xs: Seq[Sort]) {
    assert(xs.contains(t.sort),
           "Expected %s %s to be one of sorts %s, but found %s.".format(desc, t, xs, t.sort))
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, sortDesc: String, f: Sort => Boolean) {
    assert(f(t.sort),
      "Expected %s %s to be of sort %s, but found %s.".format(desc, t, sortDesc, t.sort))
  }

//  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
//  def assertSameSeqSorts(t0: Term, t1: Term) {
//    assert(
//      (t0.sort, t1.sort) match {
//        case (sorts.Seq(a), sorts.Seq(b)) if a == b => true
//        case _ => false
//      },
//      "Expected both operands to be of sort Seq(X), but found %s (%s) and %s (%s)"
//        .format(t0, t0.sort, t1, t1.sort))
//  }
}

object implicits {
  implicit def intToTerm(i: Int): IntLiteral = IntLiteral(i)

  implicit def boolToTerm(b: Boolean): BooleanLiteral = if (b) True() else False()

  implicit def fractionalPermissionsToPermissionsTuple(fp: FractionalPermissions): PermissionsTuple =
    PermissionsTuple(fp)
}