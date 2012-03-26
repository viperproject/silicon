package ch.ethz.inf.pm.silicon.state
package terms

//import scala.util.parsing.input.{Position, NoPosition}
import silAST.{ASTNode => SILASTNode}
import silAST.source.{SourceLocation => SILSourceLocation, noLocation => SILNoLocation}
// import silAST.programs.symbols.{Function => SILFunction}
// import silAST.domains.{DomainFunction => SILDomainFunction}

import ch.ethz.inf.pm.silicon
// import silicon.ast
// import silicon.ast.commonnodes
// import silicon.ast.commonnodes.{UnaryOp, BinaryOp}
// import silicon.interfaces.state.{Heap, Permission}
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

/* TODO: At least Term and Sort should go to the interfaces package.
 *       Maybe also Var and Literal.
 */
 
/* TODO: Sorts currently take not type parameters, will probably is necessary
 *       in order to support e.g. non-integer sequences.
 */
sealed trait Sort

// case class DataTypeSort(d: silAST.types.DataType) extends Sort

object sorts {
  // trait SnapshotSort extends Sort
  // trait Snap extends Sort
  object Snap extends Sort { override val toString = "Snap" }

  // trait Int extends Sort
  object Int extends Sort { override val toString = "Int" }
  // object IntSort extends IntSort { override val toString = "Int" }
  // object Int extends Sort { override val toString = "Int" }
  // val Int = DataTypeSort(silAST.types.integerType)

  // trait Bool extends Sort
  object Bool extends Sort { override val toString = "Bool" }
  // val Bool = DataTypeSort(silAST.types.booleanType)

  // trait Ref extends Sort
  object Ref extends Sort { override val toString = "Ref" }  
  // val Ref = DataTypeSort(silAST.types.referenceType)
  
  // object Perms extends Sort { override val toString = "Perm" }
  // trait Perms extends Sort
  object Perms extends Sort { override val toString = "Perms" }
  // val Perms = DataTypeSort(silAST.types.permissionType)
  
  case class UserSort(domain: silAST.domains.Domain) extends Sort {
    override val toString = domain.toString
  }
}

// object types {
  // type Boolean = Term
  // type Integer = Term[sorts.Int]
  // type Permissions = Term[sorts.Perms]
  // // type Snapshots = Term[sorts.Snap]
// }

// import sorts._
// import types._

sealed trait Term {
	/* Attention! Do not use for non-term equalities, e.g. mu == waitlevel or
	 * seq1 == seq2.
	 */
	def ≡(t: Term): Eq = Eq(this, t)
	def ≠(t: Term): Term = Not(Eq(this, t))
	
	// def convert(from: Sort, to: Sort): Term = (from, to) match {
		// // case (sor, BoolSort) => IntToBool(this)
		// // case (BoolSort, IntSort) => BoolToInt(this)
		// case (s1, s2) if s1 == s2 => this
    // case (s1, s2) => SortWrapper(this, )
		// // case (s1, s2) =>
			// // sys.error("Unexpected sort conversion %s -> %s.".format(from, to))
	// }
	
	// def convert(to: Sort): Term = convert(this.sort, to)
  
	def convert(to: Sort): Term =
    if (to == this.sort) this
    else SortWrapper(this, to)

  def sort: Sort
	
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
}

/* General sorted terms */

sealed trait IntegerTerm extends Term { override val sort = sorts.Int }
sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }
sealed trait ComparisonTerm extends BooleanTerm
sealed trait SnapshotTerm extends Term { override val sort = sorts.Snap }

sealed trait PermissionTerm extends Term {
  override val sort = sorts.Perms
  
  def *(other: Term) = PermTimes(this, other)
  def +(other: Term) = PermPlus(this, other)
  def -(other: Term) = PermMinus(this, other)
  def <(other: Term) = PermLess(this, other)
}

/* Symbols */

/* TODO: Rename to Constant/Symbol/Id */
/* case */ class Var(val id: String, val sort: Sort) extends Term {
  override val toString = id
}

object Var extends Function2[String, Sort, Var] {
  def apply(id: String, sort: Sort) = {
    val z3Id = (id.replace('#', '_')
                  .replace("τ", "$tau"))
    
    new Var(z3Id, sort)
  }
  
  def unapply(v: Var) = Some((v.id, v.sort))
}

case class FApp(val f: silAST.programs.symbols.Function,
                val s: Term,
                val t0: Term,
                val tArgs: Seq[Term],
                val sort: Sort)
    extends Term {
	
  utils.assertSort(s, "snapshot", sorts.Snap)

	override val toString =
		"FApp(%s, %s, %s, %s)".format(f.name, s, t0, tArgs.mkString(", "))
}

/* Literals */

sealed trait Literal extends Term

case object Unit extends Literal with SnapshotTerm {
  // val sort = sorts.Snap

  override val toString = "_"
 }

case class IntLiteral(n: Int) extends Literal with IntegerTerm {
	// def +(m: Int) = IntLiteral(n + m)
	// def -(m: Int) = IntLiteral(n - m)	
	// def *(m: Int) = IntLiteral(n * m)
	// def /(m: Int) = Div(this, IntLiteral(m))

	override val toString = n.toString
}

case class Null() extends Literal {
  val sort = sorts.Ref
  
  override val toString = "Null"
}

sealed trait BooleanLiteral extends Literal with BooleanTerm {
  def value: Boolean

  override def toString = value.toString
}

case class True() extends BooleanLiteral { val value = true }
case class False() extends BooleanLiteral { val value = false }

// /* Quantifiers */

// sealed trait Quantifier // extends Term { override val sort = BoolSort }

// object Forall extends Quantifier { override val toString = "∀ " }
// object Exists extends Quantifier { override val toString = "∃ " }

// case class Quantification(q: Quantifier, tVars: Seq[Var], tBody: Term) 
		// extends BooleanTerm

/* Unary operators */

sealed trait UnaryOperator extends Term {
  // def op: String
  val op = this.getClass.getSimpleName
  val t: Term

  override val toString = "%s%s".format(op, t)
}

case class Not(val t: Term) extends BooleanTerm with UnaryOperator /* with commonnodes.Not[Term] */ {
  utils.assertSort(t, "term", sorts.Bool)

	override val op = "¬"
	
	// override val toString = p match {
		// case eq: Eq => eq.p0.toString + "≠" + eq.p1.toString
		// case _ => super.toString
	// }
	
	// override def equals(other: Any) =
		// this.eq(other.asInstanceOf[AnyRef]) || (other match {
			// case Not(_p) => p == _p
			// case _ => false
		// })
}

// object Not {
	// def apply(e0: Term) = e0 match {
		// case Not(e1) => e1
		// case True() => False()
		// case False() => True()
		// case _ => new Not(e0)
	// }
	
	// def unapply(e: Not) = Some((e.p))
// }

/* Binary operators */

sealed trait BinaryOperator extends Term {
  assert(t0.sort == t1.sort, "Expected operands %s and %s to be of the same sort, but but found %s and %s.".format(t0, t1, t0.sort, t1.sort))

  // def op: String
  val op = this.getClass.getSimpleName
  val sort = t0.sort
  
  val t0: Term
  val t1: Term
  
  override val toString = "%s %s %s".format(t0, op, t1)
}

case class Plus(val t0: Term, val t1: Term)
    extends BinaryOperator with IntegerTerm
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

case class Minus(val t0: Term, val t1: Term) extends BinaryOperator with IntegerTerm
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

case class Times(val t0: Term, val t1: Term) extends BinaryOperator with IntegerTerm
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

case class Div(val t0: Term, val t1: Term) extends BinaryOperator with IntegerTerm

case class Mod(val t0: Term, val t1: Term) extends BinaryOperator with IntegerTerm

/* Boolean expression terms */		

case class Or(val t0: Term, val t1: Term) extends BinaryOperator with BooleanTerm
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

case class And(val t0: Term, val t1: Term) extends BinaryOperator with BooleanTerm
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
		
case class Implies(val t0: Term, val t1: Term) extends BinaryOperator with BooleanTerm
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

case class Iff(val t0: Term, val t1: Term) extends BinaryOperator with BooleanTerm
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

/* Comparison expression terms */

// /* TODO: Make more specific by using a generic T <: Term, so that e.g. equality
 // *       on sequences can range over SeqTerms.
 // */
// sealed trait Eq extends ComparisonTerm /* with commonnodes.Eq[Term] */ {
	// def p0: Term
	// def p1: Term
// }

case class Eq(t0: Term, t1: Term) extends BinaryOperator with ComparisonTerm /* {
  assert(p0.sort == p1.sort, "Equality Eq(%s, %s) expects both arguments to be of the same sort, but found %s and %s.".format(p0, p1, p0.sort, p1.sort))
} */

case class Less(val t0: Term, val t1: Term) extends BinaryOperator with ComparisonTerm
		/* with commonnodes.Less[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Less extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True() else False()
		// case (t0, t1) if t0 == t1 => False()
		// case _ => new Less(e0, e1)
	// }
	
	// def unapply(e: Less) = Some((e.p0, e.p1))
// }
		
case class AtMost(val t0: Term, val t1: Term) extends BinaryOperator with ComparisonTerm
		/* with commonnodes.AtMost[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object AtMost extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True() else False()
		// case (t0, t1) if t0 == t1 => True()
		// case _ => new AtMost(e0, e1)
	// }
	
	// def unapply(e: AtMost) = Some((e.p0, e.p1))
// }

case class Greater(val t0: Term, val t1: Term) extends BinaryOperator with ComparisonTerm
		/* with commonnodes.Greater[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object Greater extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True() else False()
		// case (t0, t1) if t0 == t1 => False()
		// case _ => new Greater(e0, e1)
	// }
	
	// def unapply(e: Greater) = Some((e.p0, e.p1))
// }

case class AtLeast(val t0: Term, val t1: Term) extends BinaryOperator with ComparisonTerm
		/* with commonnodes.AtLeast[Term] with commonnodes.StructuralEqualityBinOp[Term] */
		
// object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	// def apply(e0: Term, e1: Term) = (e0, e1) match {
		// case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True() else False()
		// case (t0, t1) if t0 == t1 => True()
		// case _ => new AtLeast(e0, e1)
	// }
	
	// def unapply(e: AtLeast) = Some((e.p0, e.p1))
// }

/* Other operators */

// case class Ite(val t0: Term, val t1: Term, val t2: Term) extends Term {
	// assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
			// "Ite term Ite(%s, %s, %s) is not well-sorted: %s, %s, %s"
			// .format(t0, t1, t2, t0.sort, t1.sort, t2.sort))

	// override val toString = "Ite(%s, %s, %s)".format(t0, t1, t2)
	
	// override def equals(other: Any) =
		// this.eq(other.asInstanceOf[AnyRef]) || (other match {
			// case Ite(_t0, _t1, _t2) => t0 == _t0 && t1 == _t1 && t2 == _t2
			// case _ => false
		// })
    
  // override val sort = t1.sort
// }

// object Ite extends Function3[Term, Term, Term, Term] {
	// def apply(e0: Term, e1: Term, e2: Term) = e0 match {
		// case True() => e1
		// case False() => e2
		// case _ => new Ite(e0, e1, e2)
	// }
	
	// def unapply(e: Ite) = Some((e.t0, e.t1, e.t2))	
// }

/* Permissions */

// sealed trait Permissions extends Term[sorts.Perms] {
  // val sort = sorts.Perms
  
  // // def * (p: Permissions) = PermTimes(this, p)
  // // def + (p: Permissions) = PermPlus(this, p)
  // // def - (p: Permissions) = PermMinus(this, p)
// }

case class FullPerms() extends PermissionTerm { override val toString = "Full" }
case class ZeroPerms() extends PermissionTerm { override val toString = "Zero" }
case class EpsPerms() extends PermissionTerm { override val toString = "Eps" }

/* case */ class Perms(val t: Term) extends PermissionTerm {
  utils.assertSort(t, "term", sorts.Perms)

  override val toString = "Perms(%s)".format(t)
}

object Perms extends Function1[Term, PermissionTerm] {
  def apply(t: Term) = t match {
    case tp @ Perms(_) => tp
    case _ => new Perms(t)
  }
  
  def unapply(tp: Perms) = Some(tp.t)
}

/* case */ class PermTimes(val t0: Term, val t1: Term) extends BinaryOperator with PermissionTerm

object PermTimes extends Function2[Term, Term, PermissionTerm] {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (FullPerms(), t) => Perms(t)
    case (t, FullPerms()) => Perms(t)
    case (ZeroPerms(), _) => ZeroPerms()
    case (_, ZeroPerms()) => ZeroPerms()
    case (_, _) => new PermTimes(t0, t1)
  }
  
  def unapply(pt: PermTimes) = Some((pt.t0, pt.t1))
}

/* case */ class PermPlus(val t0: Term, val t1: Term) extends BinaryOperator with PermissionTerm

object PermPlus extends Function2[Term, Term, PermissionTerm] {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (ZeroPerms(), t) => Perms(t)
    case (t, ZeroPerms()) => Perms(t)
    case (_, _) => new PermPlus(t0, t1)
  }
  
  def unapply(pp: PermPlus) = Some((pp.t0, pp.t1))
}

/* case */ class PermMinus(val t0: Term, val t1: Term) extends BinaryOperator with PermissionTerm

object PermMinus extends Function2[Term, Term, PermissionTerm] {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (p, ZeroPerms()) => Perms(p)
    case (p0, p1) if p0 == p1 => ZeroPerms()
    case (_, _) => new PermMinus(t0, t1)
  }
  
  def unapply(pm: PermMinus) = Some((pm.t0, pm.t1))
}

/* case */ class PermLess(val t0: Term, val t1: Term) extends BinaryOperator with BooleanTerm {
  override val toString = "%s < %s".format(t0, t1)
}

object PermLess extends Function2[Term, Term, BooleanTerm] {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (t0, t1) if t0 == t1 => False()
    case (_, _) => new PermLess(t0, t1)
  }
  
  def unapply(pl: PermLess) = Some((pl.t0, pl.t1))
}

/* Domains */

case class DomainFApp(val f: silAST.domains.DomainFunction,
                      val tArgs: Seq[Term],
                      val sort: Sort)
    extends Term {

  override val toString = f.name + tArgs.mkString("(", ", ", ")")
}

case class DomainPApp(val p: silAST.domains.DomainPredicate,
                      val tArgs: Seq[Term])
    extends BooleanTerm {

  override val toString = p.name + tArgs.mkString("(", ", ", ")")
}

/* Auxiliary terms */

case class Combine(t0: Term, t1: Term) extends BinaryOperator with SnapshotTerm {
  // val sort = sorts.Snap

  override val toString = "(%s, %s)".format(t0, t1)
}

// /* TODO: Can't we replace SnapEq? It is only relevant in the final translation
 // *       to Z3.
 // */
// case class SnapEq(p0: Term, p1: Term) extends Eq

// sealed trait SortWrapper extends Term { def t0: Term }

case class SortWrapper(t: Term, to: Sort) extends Term {
  override val toString = "(%s) %s".format(to, t)
  override val sort = to
}

// case class BoolToInt(t0: Term) extends SortWrapper { val sort = sorts.Int }
// case class IntToBool(t0: Term) extends SortWrapper { val sort = sorts.Bool }

// case class UpdateMap(id: String, t: Term, n: Int) extends LockTerm
	// { override val toString = "%s[%s,%s]".format(id, t, n) }

/* Utility functions */

object utils {
	def ¬(t: Term) = Not(t)

	def BigAnd(it: Iterable[Term], f: Term => Term = t => t) =
		mapReduceLeft(it, f, And, True())

	def BigOr(it: Iterable[Term], f: Term => Term = t => t) =
		mapReduceLeft(it, f, Or, True())
    
  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  private[terms] def assertSort(t: Term, desc: String, s: Sort) {
    assert(t.sort == s, "Expected %s %s to be of sort %s, but found %s.".format(desc, t, s, t.sort))
  }
}

/* A DSL facilitating working with Terms */

// object dsl {
  // case class TermOperand private[dsl](t: Term) {
    // def +(other: TermOperand) = TermOperand(Plus(t, other.t))
    // def -(other: TermOperand) = TermOperand(Minus(t, other.t))
    // def *(other: TermOperand) = TermOperand(Times(t, other.t))
    
    // def <(other: TermOperand) = TermOperand(Less(t, other.t))
  // }

  // implicit def termToTermOperand(t: Term): TermOperand = 
    // TermOperand(t)
  
  // implicit def termOperandToTerm(ato: TermOperand): Term =
    // ato.t
  
  // implicit def termToPermissionTerm(t: Term): PermissionTerm =
    // wrapTermInPerms(t)
    
  // implicit def termOperandToPermissions(ato: TermOperand): PermissionTerm =
    // wrapTermInPerms(ato.t)
  
  // private[dsl] def wrapTermInPerms(t: Term): PermissionTerm = {
    // utils.assertSort(t, "term", sorts.Perms)
    // t
  // }
// }