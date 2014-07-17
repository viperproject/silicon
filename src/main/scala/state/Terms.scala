/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state.terms

import scala.reflect._
import ast.commonnodes
import silver.ast.utility.Visitor

/* Why not have a Term[S <: Sort]?
 * Then we cannot have optimising extractor objects anymore, because these
 * don't take type parameters. However, defining a DSL seems to only be
 * possible when Term can be parameterised ...
 * Hm, reusing e.g. Times for Ints and Perm seems to be problematic w.r.t.
 * to optimising extractor objects because the optimisations depend on the
 * sort, e.g. IntLiteral(a) * IntLiteral(b) ~~> IntLiteral(a * b),
 *            Perm(t) * FullPerm() ~~> Perm(t)
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

/*
 * Sorts
 */

sealed trait Sort extends Symbol

object sorts {
  import scala.collection.{Seq => SISeq}

  object Snap extends Sort { val id = "Snap"; override val toString = id }
  object Int extends Sort { val id = "Int"; override val toString = id }
  object Bool extends Sort { val id = "Bool"; override val toString = id }
  object Ref extends Sort { val id = "Ref"; override val toString = id }
  object Perm extends Sort { val id = "Perm"; override val toString = id }
  object Unit extends Sort { val id = "()"; override val toString = "()" }

  case class Seq(elementsSort: Sort) extends Sort {
    val id = "Seq[%s]".format(elementsSort)
    override val toString = id
  }

  case class Set(elementsSort: Sort) extends Sort {
    val id = "Set[%s]".format(elementsSort)
    override val toString = id
  }

  case class Multiset(elementsSort: Sort) extends Sort {
    val id = "Multiset[%s]".format(elementsSort)
    override val toString = id
  }

  class Arrow private (val from: SISeq[Sort], val to: Sort) extends Sort {
    val id = s"${from mkString " x "} -> $to"

    override val hashCode = silicon.utils.generateHashCode(from, to)

    override def equals(other: Any) =
      this.eq(other.asInstanceOf[AnyRef]) || (other match {
        case a: Arrow => this.from == a.from && this.to == a.to
        case _ => false
      })

    override val toString = id
  }

  object Arrow extends ((SISeq[Sort], Sort) => Sort) {
    def apply(from: SISeq[Sort], to: Sort) = {
      val actualFrom = from match {
        case SISeq() => SISeq(sorts.Unit)
        case SISeq(sorts.Unit) => from
        case other =>
          Predef.assert(!other.contains(sorts.Unit), "")
          other
      }

      new Arrow(actualFrom, to)
    }

    def apply(from: Sort, to: Sort) = new Arrow(List(from), to)

    def unapply(arrow: Arrow) = Some((arrow.from, arrow.to))
  }

  case class UserSort(id: String) extends Sort {
    override val toString = id
  }
}

/*
 * Declarations
 */

sealed trait Decl

case class VarDecl(v: Var) extends Decl
case class SortDecl(sort: Sort) extends Decl
case class FunctionDecl(func: Function) extends Decl
case class SortWrapperDecl(from: Sort, to: Sort) extends Decl

/*
 * Basic terms
 */

/* TODO: Should extend viper.silver.ast.Node in order to share all the
 *       visitor-related methods.
 *       To do this, Node has to be made parametric in the type of concrete
 *       Nodes that the visitors operate on. Also, the 'subnodes/subterms'
 *       function must be customizable.
 */
sealed trait Term /*extends Traversable[Term]*/ {
  def sort: Sort

  def ===(t: Term): Term = Eq(this, t)

  def !==(t: Term): Term = Not(Eq(this, t))

  def convert(to: Sort): Term = SortWrapper(this, to)

  def visit[A](f: PartialFunction[Term, A]) =
    Visitor.visit(this, state.utils.subterms)(f)

  def transform(pre: PartialFunction[Term, Term] = PartialFunction.empty)
               (recursive: Term => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[Term, Term] = PartialFunction.empty)
               : this.type =

    state.utils.transform[this.type](this, pre)(recursive, post)

  def existsDefined[A](f: PartialFunction[Term, A]): Boolean =
    Visitor.existsDefined(this, state.utils.subterms, f)

  def replace(original: Term, replacement: Term): Term =
    this.transform{case `original` => replacement}()

  def replace[T <: Term : ClassTag](replacements: Map[T, Term]): Term = {
    this.transform{case t: T if replacements.contains(t) => replacements(t)}()
  }

  def replace(originals: Seq[Term], replacements: Seq[Term]): Term = {
    this.replace(toMap(originals.zip(replacements)))
  }
}

/* Symbols */

sealed trait Symbol {
  def id: String
}

case class Var(id: String, sort: Sort) extends Symbol with Term {
  override val toString = id
}

class Function(val id: String, val sort: sorts.Arrow) extends Symbol with Term {
  override val hashCode = silicon.utils.generateHashCode(id, sort)

  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case f: Function => this.id == f.id && this.sort == f.sort
      case _ => false
    })

  override val toString = s"$id: $sort"
}

object Function {
  def apply(id: String, sort: sorts.Arrow) = new Function(id, sort)

  def apply(id: String, argSorts: Seq[Sort], toSort: Sort) = {
    val symbolSort = sorts.Arrow(argSorts, toSort)

    new Function(id, symbolSort)
  }

  def unapply(f: Function) = Some((f.id, f.sort))
}

/* Literals */

sealed trait Literal extends Term

case object Unit extends SnapshotTerm with Literal {
  override val toString = "_"
}

case class IntLiteral(n: BigInt) extends ArithmeticTerm with Literal {
	def +(m: Int) = IntLiteral(n + m)
	def -(m: Int) = IntLiteral(n - m)
	def *(m: Int) = IntLiteral(n * m)
	def /(m: Int) = Div(this, IntLiteral(m))
	override val toString = n.toString
}

case class Null() extends Term with Literal {
  val sort = sorts.Ref
  override val toString = "Null"
}

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

case class Trigger(ts: Seq[Term])

/* Placeholder */
case class *() extends Symbol with Term {
  val id = "*"
  val sort = sorts.Ref

  override val toString = "*"
}

case class Quantification(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger] = Seq())
    extends BooleanTerm

/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
		with commonnodes.Plus[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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
		with commonnodes.Minus[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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
		with commonnodes.Times[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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

class Not(val p: Term) extends BooleanTerm with commonnodes.StructuralEqualityUnaryOp[Term] {
	override val op = "!"

	override val toString = p match {
		case eq: Eq => eq.p0.toString + " != " + eq.p1.toString
		case _ => super.toString
	}
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
		with commonnodes.Or[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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
		with commonnodes.And[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

object And extends Function2[Term, Term, Term] {
	def apply(el: Term, er: Term) = (el, er) match {
		case (True(), e1) => e1
		case (e0, True()) => e0
		case (False(), _) | (_, False()) => False()
		case (e0, e1) if e0 == e1 => e0
    case (e0, Implies(e1, e2)) if e0 == e1 =>
      /* This case arises quite often during local evaluation of expressions. */
      new And(e0, e2)
		case _ => new And(el, er)
	}

	def unapply(e: And) = Some((e.p0, e.p1))
}

class Implies(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Implies[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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
		with commonnodes.Iff[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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

	override val toString = "%s ? %s : %s".format(t0, t1, t2)

  override val hashCode = silicon.utils.generateHashCode(t0, t1, t2)

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
    case _ if e1 == e2 => e1
		case _ => new Ite(e0, e1, e2)
	}

	def unapply(e: Ite) = Some((e.t0, e.t1, e.t2))
}

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

case class Eq(p0: Term, p1: Term, specialize: Boolean = true) extends ComparisonTerm with commonnodes.Eq[Term] {
  assert(p0.sort == p1.sort,
         "Expected both operands to be of the same sort, but found %s (%s) and %s (%s)."
         .format(p0.sort, p0, p1.sort, p1))
}

class Less(val p0: Term, val p1: Term)
      extends ComparisonTerm with commonnodes.Less[Term] with commonnodes.StructuralEqualityBinaryOp[Term] {

  assert(p0.sort == p1.sort,
    "Expected both operands to be of the same sort, but found %s (%s) and %s (%s)."
      .format(p0.sort, p0, p1.sort, p1))
}

object Less extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True() else False()
		case (t0, t1) if t0 == t1 => False()
		case _ => new Less(e0, e1)
	}

	def unapply(e: Less) = Some((e.p0, e.p1))
}

class AtMost(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.AtMost[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

object AtMost extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True() else False()
		case (t0, t1) if t0 == t1 => True()
		case _ => new AtMost(e0, e1)
	}

	def unapply(e: AtMost) = Some((e.p0, e.p1))
}

class Greater(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.Greater[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

object Greater extends /* OptimisingBinaryArithmeticOperation with */ Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True() else False()
		case (t0, t1) if t0 == t1 => False()
		case _ => new Greater(e0, e1)
	}

	def unapply(e: Greater) = Some((e.p0, e.p1))
}

class AtLeast(val p0: Term, val p1: Term) extends ComparisonTerm
		with commonnodes.AtLeast[Term] with commonnodes.StructuralEqualityBinaryOp[Term]

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

sealed trait FractionalPermissions[P <: FractionalPermissions[P]] extends Term {
  def +(other: P): P
  def -(other: P): P
  def *(other: P): P
  def <(other: P): BooleanTerm
  def >(other: P): BooleanTerm
}

sealed abstract class DefaultFractionalPermissions extends FractionalPermissions[DefaultFractionalPermissions] {
  val sort = sorts.Perm

  def +(other: DefaultFractionalPermissions) = PermPlus(this, other)
  def -(other: DefaultFractionalPermissions) = PermMinus(this, other)
  def *(other: DefaultFractionalPermissions) = PermTimes(this, other)
  def <(other: DefaultFractionalPermissions) = PermLess(this, other)
  def >(other: DefaultFractionalPermissions) = PermLess(other, this)
}

case class NoPerm() extends DefaultFractionalPermissions { override val toString = "Z" }
case class FullPerm() extends DefaultFractionalPermissions { override val toString = "W" }
case class FractionPerm(n: DefaultFractionalPermissions, d: DefaultFractionalPermissions) extends DefaultFractionalPermissions { override val toString = s"$n/$d" }
case class WildcardPerm(v: Var) extends DefaultFractionalPermissions { override val toString = v.toString }

case class TermPerm(t: Term) extends DefaultFractionalPermissions {
  utils.assertSort(t, "term", List(sorts.Perm, sorts.Int))

  override val toString = t.toString
}

case class IsValidPermVar(v: Var) extends BooleanTerm {
  override val toString = s"PVar($v)"
}

case class IsReadPermVar(v: Var, ub: DefaultFractionalPermissions) extends BooleanTerm {
  override val toString = s"RdVar($v, $ub)"
}

class PermTimes(val p0: DefaultFractionalPermissions, val p1: DefaultFractionalPermissions)
    extends DefaultFractionalPermissions
       with commonnodes.Times[DefaultFractionalPermissions]
       with commonnodes.StructuralEqualityBinaryOp[DefaultFractionalPermissions]

object PermTimes extends ((DefaultFractionalPermissions, DefaultFractionalPermissions) => DefaultFractionalPermissions) {
  def apply(t0: DefaultFractionalPermissions, t1: DefaultFractionalPermissions) = (t0, t1) match {
    case (FullPerm(), t) => t
    case (t, FullPerm()) => t
    case (NoPerm(), _) => NoPerm()
    case (_, NoPerm()) => NoPerm()
    case (_, _) => new PermTimes(t0, t1)
  }

  def unapply(pt: PermTimes) = Some((pt.p0, pt.p1))
}

class IntPermTimes(val p0: Term, val p1: DefaultFractionalPermissions)
    extends DefaultFractionalPermissions
       with commonnodes.Times[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]

object IntPermTimes extends ((Term, DefaultFractionalPermissions) => DefaultFractionalPermissions) {
  val One = IntLiteral(1)

  def apply(t0: Term, t1: DefaultFractionalPermissions) = (t0, t1) match {
    case (One, t) => t
    case (_, NoPerm()) => NoPerm()
    case (_, _) => new IntPermTimes(t0, t1)
  }

  def unapply(pt: IntPermTimes) = Some((pt.p0, pt.p1))
}

class PermPlus(val p0: DefaultFractionalPermissions, val p1: DefaultFractionalPermissions)
    extends DefaultFractionalPermissions
       with commonnodes.Plus[DefaultFractionalPermissions]
       with commonnodes.StructuralEqualityBinaryOp[DefaultFractionalPermissions]

object PermPlus extends ((DefaultFractionalPermissions, DefaultFractionalPermissions) => DefaultFractionalPermissions) {
  def apply(t0: DefaultFractionalPermissions, t1: DefaultFractionalPermissions) = (t0, t1) match {
    case (NoPerm(), _) => t1
    case (_, NoPerm()) => t0
    case (_, _) => new PermPlus(t0, t1)
  }

  def unapply(pp: PermPlus) = Some((pp.p0, pp.p1))
}

class PermMinus(val p0: DefaultFractionalPermissions, val p1: DefaultFractionalPermissions)
    extends DefaultFractionalPermissions
       with commonnodes.Minus[DefaultFractionalPermissions]
       with commonnodes.StructuralEqualityBinaryOp[DefaultFractionalPermissions] {

  override val toString = p1 match {
    case _: commonnodes.BinaryOp[_] => s"$p0 $op ($p1)"
    case _ => s"$p0 $op $p1"
  }
}

object PermMinus extends ((DefaultFractionalPermissions, DefaultFractionalPermissions) => DefaultFractionalPermissions) {
  def apply(t0: DefaultFractionalPermissions, t1: DefaultFractionalPermissions) = (t0, t1) match {
    case (_, NoPerm()) => t0
    case (p0, p1) if p0 == p1 => NoPerm()
    case (p0, PermMinus(p1, p2)) if p0 == p1 => p2
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => new PermMinus(t0, t1)
  }

  def unapply(pm: PermMinus) = Some((pm.p0, pm.p1))
}

class PermLess(val p0: DefaultFractionalPermissions, val p1: DefaultFractionalPermissions)
    extends BooleanTerm
       with commonnodes.Less[DefaultFractionalPermissions]
       with commonnodes.StructuralEqualityBinaryOp[DefaultFractionalPermissions] {

  override val toString = "(%s) < (%s)".format(p0, p1)
}

object PermLess extends ((DefaultFractionalPermissions, DefaultFractionalPermissions) => BooleanTerm) {
  def apply(t0: DefaultFractionalPermissions, t1: DefaultFractionalPermissions) = (t0, t1) match {
    case (t0, t1) if t0 == t1 => False()
    case (_, _) => new PermLess(t0, t1)
  }

  def unapply(pl: PermLess) = Some((pl.p0, pl.p1))
}

case class PermMin(p0: Term, p1: Term) extends DefaultFractionalPermissions with commonnodes.BinaryOp[Term] {
  utils.assertSort(p0, "Permission 1st", sorts.Perm)
  utils.assertSort(p1, "Permission 2nd", sorts.Perm)

  override val toString = s"min ($p0, $p1)"
}

/* Functions */

case class Apply(func: Term, args: Seq[Term]) extends Term {
  val funcSort = func.sort match {
    case a: sorts.Arrow => a
    case other => sys.error(s"Cannot apply $func of sort $other to $args")
  }

  val sort = funcSort.to

  override val toString = s"$func(${args.mkString(",")})"
}

case class FApp(function: Function, snapshot: Term, tArgs: Seq[Term]) extends Term {
  utils.assertSort(snapshot, "snapshot", sorts.Snap)

  val sort = function.sort.to
  override val toString = s"${function.id}(${tArgs.mkString(",")};$snapshot)"
}

/* Sequences */

/* TODO: Make arguments more specific, i.e., SeqTerm instead of Term. The problem is that terms.Var can be
 *       used there, as well as terms.FApp, and probably other terms that are not SeqTerms but of sort Seq.
 *       How to deal with those?
 */

sealed trait SeqTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Seq
}

case class SeqRanged(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
  utils.assertSort(p0, "first operand", sorts.Int)
  utils.assertSort(p1, "second operand", sorts.Int)

  val elementsSort = sorts.Int
  val sort = sorts.Seq(elementsSort)

  override val toString = "[%s..%s]".format(p0, p1)
}

case class SeqNil(elementsSort: Sort) extends SeqTerm with Literal {
  val sort = sorts.Seq(elementsSort)
  override val toString = "Nil"
}

case class SeqSingleton(p: Term) extends SeqTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Seq(elementsSort)

  override val toString = "[" + p + "]"
}

class SeqAppend(val p0: Term, val p1: Term) extends SeqTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val op = "++"
}

object SeqAppend extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSeqSorts(t0, t1)
    new SeqAppend(t0, t1)
  }

  def unapply(sa: SeqAppend) = Some((sa.p0, sa.p1))
}

class SeqDrop(val p0: Term, val p1: Term) extends SeqTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val toString = p0 + "[" + p1 + ":]"
}

object SeqDrop extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqDrop(t0, t1)
  }

  def unapply(sd: SeqDrop) = Some((sd.p0, sd.p1))
}

class SeqTake(val p0: Term, val p1: Term) extends SeqTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val toString = p0 + "[:" + p1 + "]"
}

object SeqTake extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqTake(t0, t1)
  }

  def unapply(st: SeqTake) = Some((st.p0, st.p1))
}

class SeqLength(val p: Term) extends Term with commonnodes.StructuralEqualityUnaryOp[Term] {
  val sort = sorts.Int
  override val toString = "|" + p + "|"
}

object SeqLength {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Seq", _.isInstanceOf[sorts.Seq])
    new SeqLength(t)
  }

  def unapply(sl: SeqLength) = Some((sl.p))
}

class SeqAt(val p0: Term, val p1: Term) extends Term with commonnodes.StructuralEqualityBinaryOp[Term] {
  val sort = p0.sort.asInstanceOf[sorts.Seq].elementsSort

  override val toString = p0 + "[" + p1 + "]"
}

object SeqAt extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqAt(t0, t1)
  }

  def unapply(sa: SeqAt) = Some((sa.p0, sa.p1))
}

class SeqIn(val p0: Term, val p1: Term) extends BooleanTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  override val toString = "%s in %s".format(p1, p0)
}

object SeqIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    new SeqIn(t0, t1)
  }

  def unapply(si: SeqIn) = Some((si.p0, si.p1))
}

class SeqUpdate(val t0: Term, val t1: Term, val t2: Term) extends SeqTerm {
  val sort = t0.sort.asInstanceOf[sorts.Seq]
  val elementsSort = sort.elementsSort

  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case su: SeqUpdate if su.getClass.eq(this.getClass) => t0 == su.t0 && t1 == su.t1 && t2 == su.t2
      case _ => false
    })

  override def hashCode(): Int = silicon.utils.generateHashCode(t0, t1, t2)

  override val toString = s"$t0[$t1] := $t2".format(t0, t1, t2)
}

object SeqUpdate extends ((Term, Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term, t2: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    utils.assertSort(t2, "third operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)

    new SeqUpdate(t0, t1, t2)
  }

  def unapply(su: SeqUpdate) = Some((su.t0, su.t1, su.t2))
}

/* Sets */

sealed trait SetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Set
}

sealed trait BinarySetOp extends SetTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)
}

case class EmptySet(elementsSort: Sort) extends SetTerm with Literal {
  val sort = sorts.Set(elementsSort)
  override val toString = "Ø"
}

case class SingletonSet(p: Term) extends SetTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Set(elementsSort)

  override val toString = "{" + p + "}"
}

class SetAdd(val p0: Term, val p1: Term) extends SetTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)

  override val op = "+"
}

object SetAdd extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Set].elementsSort)

    new SetAdd(t0, t1)
  }

  def unapply(sa: SetAdd) = Some((sa.p0, sa.p1))
}

class SetUnion(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "∪"
}

object SetUnion extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetUnion(t0, t1)
  }

  def unapply(su: SetUnion) = Some((su.p0, su.p1))
}

class SetIntersection(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "∩"
}

object SetIntersection extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetIntersection(t0, t1)
  }

  def unapply(si: SetIntersection) = Some((si.p0, si.p1))
}

class SetSubset(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "⊂"
}

object SetSubset extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetSubset(t0, t1)
  }

  def unapply(ss: SetSubset) = Some((ss.p0, ss.p1))
}

class SetDisjoint(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "disj"
}

object SetDisjoint extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetDisjoint(t0, t1)
  }

  def unapply(sd: SetDisjoint) = Some((sd.p0, sd.p1))
}

class SetDifference(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "\\"
}

object SetDifference extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetDifference(t0, t1)
  }

  def unapply(sd: SetDifference) = Some((sd.p0, sd.p1))
}

class SetIn(val p0: Term, val p1: Term) extends BooleanTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  override val op = "in"
}

object SetIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t1, "second operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Set].elementsSort)

    new SetIn(t0, t1)
  }

  def unapply(si: SetIn) = Some((si.p0, si.p1))
}

class SetCardinality(val p: Term) extends Term with commonnodes.StructuralEqualityUnaryOp[Term] {
  val sort = sorts.Int
  override val toString = "|" + p + "|"
}

object SetCardinality {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Set", _.isInstanceOf[sorts.Set])
    new SetCardinality(t)
  }

  def unapply(sc: SetCardinality) = Some((sc.p))
}

/* Multisets */

sealed trait MultisetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Multiset
}

sealed trait BinaryMultisetOp extends MultisetTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

class MultisetUnion(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∪"
}

object MultisetUnion extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameMultisetSorts(t0, t1)
    new MultisetUnion(t0, t1)
  }

  def unapply(mu: MultisetUnion) = Some((mu.p0, mu.p1))
}

class MultisetIntersection(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∩"
}

object MultisetIntersection extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameMultisetSorts(t0, t1)
    new MultisetIntersection(t0, t1)
  }

  def unapply(mi: MultisetIntersection) = Some((mi.p0, mi.p1))
}

class MultisetSubset(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "⊂"
}

object MultisetSubset extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameMultisetSorts(t0, t1)
    new MultisetSubset(t0, t1)
  }

  def unapply(ms: MultisetSubset) = Some((ms.p0, ms.p1))
}

class MultisetDifference(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "\\"
}

object MultisetDifference extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameMultisetSorts(t0, t1)
    new MultisetDifference(t0, t1)
  }

  def unapply(md: MultisetDifference) = Some((md.p0, md.p1))
}

class MultisetIn(val p0: Term, val p1: Term) extends BooleanTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  override val op = "∈"
}

object MultisetIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t1, "second operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetIn(t0, t1)
  }

  def unapply(mi: MultisetIn) = Some((mi.p0, mi.p1))
}

class MultisetCardinality(val p: Term) extends Term with commonnodes.StructuralEqualityUnaryOp[Term] {
  val sort = sorts.Int
  override val toString = "|" + p + "|"
}

object MultisetCardinality {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Multiset", _.isInstanceOf[sorts.Multiset])
    new MultisetCardinality(t)
  }

  def unapply(mc: MultisetCardinality) = Some((mc.p))
}

class MultisetCount(val p0: Term, val p1: Term) extends Term with commonnodes.StructuralEqualityBinaryOp[Term] {
  val sort = sorts.Int
  override val toString = s"cnt($p0,$p1)"
}

object MultisetCount extends {
  def apply(e: Term, t: Term) = {
    utils.assertSort(t, "second operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(e, "first operand", t.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetCount(e,t)
  }

  def unapply(mc:MultisetCount) = Some((mc.p0, mc.p1))
}

class MultisetFromSeq(val p: Term) extends Term with commonnodes.StructuralEqualityUnaryOp[Term] {
  val elementsSort = p.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

object MultisetFromSeq {
  def apply(p:Term) = {
    utils.assertSort(p, "first operand", "Seq", _.isInstanceOf[sorts.Seq])

    new MultisetFromSeq(p)
  }

  def unapply(m:MultisetFromSeq) = Some(m.p)
}

/* Domains */

case class DomainFApp(function: Function, tArgs: Seq[Term]) extends Term {
  val sort = function.sort.to
  override val toString = function.id + tArgs.mkString("(", ", ", ")")
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

class Combine(val p0: Term, val p1: Term) extends SnapshotTerm with commonnodes.StructuralEqualityBinaryOp[Term] {
  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)

  override val toString = s"($p0, $p1)"
}

object Combine {
  def apply(t0: Term, t1: Term) = new Combine(t0.convert(sorts.Snap), t1.convert(sorts.Snap))

  def unapply(c: Combine) = Some((c.p0, c.p1))
}

case class First(t: Term) extends SnapshotTerm {
  utils.assertSort(t, "term", sorts.Snap)
}

case class Second(t: Term) extends SnapshotTerm {
  utils.assertSort(t, "term", sorts.Snap)
}

/* Nasty internals */

class SortWrapper(val t: Term, val to: Sort) extends Term {
  assert((t.sort == sorts.Snap || to == sorts.Snap) && t.sort != to,
         s"Unexpected sort wrapping of $t from ${t.sort} to $to")

  override val hashCode = silicon.utils.generateHashCode(t, to)

  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case sw: SortWrapper => this.t == sw.t && this.to == sw.to
      case _ => false
    })

  override val toString = s"$t"
  override val sort = to
}

object SortWrapper {
  def apply(t: Term, to: Sort) = t match {
    case _ if t.sort == to => t
    case sw: SortWrapper if sw.t.sort == to => sw.t
    case _ => new SortWrapper(t, to)
  }

  def unapply(sw: SortWrapper) = Some((sw.t, sw.to))
}

/* Other terms */

class Distinct(val ts: Set[Term]) extends BooleanTerm {
  assert(ts.nonEmpty, "Distinct requires at least term.")

  override val toString = s"Distinct($ts)"

  override val hashCode = ts.hashCode

  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case d: Distinct if d.getClass.eq(this.getClass) =>
        /* getClass identity is checked in order to prevent that different
         * subtypes of Distinct are considered equal.
         */
        ts == d.ts

      case _ => false
    })
}

object Distinct {
  def apply(ts: Set[Term]): Term =
    if (ts.nonEmpty) new Distinct(ts)
    else True()

  def unapply(d: Distinct) = Some(d.ts)
}

class NullTrigger(val t:Term) extends BooleanTerm {
  override val toString = s"Null($t)"
  assert(t.sort == sorts.Ref)
}

object NullTrigger {
  def apply(t:Term):Term =
    new NullTrigger(t)

  def unapply(n:NullTrigger) = Some(n.t)
}

/* Convenience functions */

object perms {
  def IsNonNegative(p: DefaultFractionalPermissions) = p match {
    case _: NoPerm | _: FullPerm | _: WildcardPerm => True()
    case _ => Or(p === NoPerm(), NoPerm() < p)
  }

  def IsPositive(p: DefaultFractionalPermissions) = p match {
    case _: NoPerm => False() /* TODO: This "false" should not be checked; asserting it should just return false/no */
    case _: FullPerm | _: WildcardPerm => True()
    case _ => NoPerm() < p
  }

  def IsAsPermissive(p1: DefaultFractionalPermissions, p2: DefaultFractionalPermissions) =
    if (p1 == p2) True()
    else Or(p1 === p2, p2 < p1)

  def IsNoAccess(p: DefaultFractionalPermissions) = p match {
    case _: NoPerm => True()
    case  _: PermPlus | PermMinus(_, _: WildcardPerm) => False() /* TODO: This "false" should not be checked; asserting it should just return false/no */
      /* ATTENTION: This is only sound if both plus operands and the left minus operand are positive! */
    case _ => Or(p === NoPerm(), p < NoPerm())
  }
}

/* Utility functions */

object utils {
  def ¬(t: Term) = Not(t)

  def BigAnd(it: Iterable[Term], f: Term => Term = t => t) =
    silicon.utils.mapReduceLeft(it, f, And, True())

  def BigOr(it: Iterable[Term], f: Term => Term = t => t): Term =
    silicon.utils.mapReduceLeft(it, f, Or, True())

  def BigPermSum(it: Iterable[DefaultFractionalPermissions],
                 f: DefaultFractionalPermissions => DefaultFractionalPermissions = t => t)
                : DefaultFractionalPermissions =

    silicon.utils.mapReduceLeft(it, f, PermPlus, NoPerm())

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

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSameSeqSorts(t0: Term, t1: Term) {
    assert(
      (t0.sort, t1.sort) match {
        case (sorts.Seq(a), sorts.Seq(b)) if a == b => true
        case _ => false
      },
      "Expected both operands to be of sort Seq(X), but found %s (%s) and %s (%s)"
        .format(t0, t0.sort, t1, t1.sort))
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSameSetSorts(t0: Term, t1: Term) {
    assert(
      (t0.sort, t1.sort) match {
        case (sorts.Set(a), sorts.Set(b)) if a == b => true
        case _ => false
      },
      "Expected both operands to be of sort Set(X), but found %s (%s) and %s (%s)"
        .format(t0, t0.sort, t1, t1.sort))
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSameMultisetSorts(t0: Term, t1: Term) {
    assert(
      (t0.sort, t1.sort) match {
        case (sorts.Multiset(a), sorts.Multiset(b)) if a == b => true
        case _ => false
      },
      "Expected both operands to be of sort Multiset(X), but found %s (%s) and %s (%s)"
        .format(t0, t0.sort, t1, t1.sort))
  }
}

object implicits {
  import scala.language.implicitConversions

  implicit def intToTerm(i: Int): IntLiteral = IntLiteral(i)
  implicit def boolToTerm(b: Boolean): BooleanLiteral = if (b) True() else False()
}
