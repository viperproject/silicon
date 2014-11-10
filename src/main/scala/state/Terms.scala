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
import silver.ast.utility.{GenericTriggerGenerator, Visitor}

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
  object Unit extends Sort { val id = "()"; override val toString = id }

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

  class Arrow private (val from: SISeq[Sort], val to: Sort) extends Sort
      with commonnodes.StructuralEquality {

    val equalityDefiningMembers = from :: to :: Nil
    val id = s"${from mkString " x "} -> $to"
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

  def ===(t: Term): Term = Equals(this, t)
  def !==(t: Term): Term = Not(Equals(this, t))

  def convert(to: Sort): Term = SortWrapper(this, to)

  lazy val subterms = state.utils.subterms(this)

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[Term, Any]) =
    Visitor.visit(this, state.utils.subterms)(f)

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[R](f: (Term, Seq[R]) => R) = Visitor.reduceTree(this, state.utils.subterms)(f)

  /** @see [[Visitor.existsDefined()]] */
  def existsDefined(f: PartialFunction[Term, Any]): Boolean =
    Visitor.existsDefined(this, state.utils.subterms)(f)

  /** @see [[Visitor.hasSubnode()]] */
  def hasSubterm(subterm: Term): Boolean = Visitor.hasSubnode(this, subterm, state.utils.subterms)

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[R](f: PartialFunction[Term, R]) : Seq[R] =
    Visitor.deepCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[Visitor.find()]] */
  def find[R](f: PartialFunction[Term, R]): Option[R] =
    Visitor.find(this, state.utils.subterms)(f)

  /** @see [[state.utils.transform()]] */
  def transform(pre: PartialFunction[Term, Term] = PartialFunction.empty)
               (recursive: Term => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[Term, Term] = PartialFunction.empty)
  : this.type =

    state.utils.transform[this.type](this, pre)(recursive, post)

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

class Function(val id: String, val sort: sorts.Arrow)
    extends Symbol
       with Term
       with commonnodes.StructuralEquality {

  lazy val limitedVersion = Function(id + "$", sort)
  val equalityDefiningMembers = id :: sort :: Nil
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
	override val toString = n.toString()
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

object Forall extends Quantifier {
  def apply(qvar: Var, tBody: Term, trigger: Trigger) =
    Quantification(Forall, qvar :: Nil, tBody, trigger :: Nil)

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Forall, qvar :: Nil, tBody, triggers)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger) =
    Quantification(Forall, qvars, tBody, trigger :: Nil)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Forall, qvars, tBody, triggers)

  override val toString = "QA"
}

object Exists extends Quantifier {
  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvar :: Nil, tBody, triggers)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvars, tBody, triggers)

  override val toString = "QE"
}

class Trigger private[terms] (val p: Seq[Term]) extends commonnodes.StructuralEqualityUnaryOp[Seq[Term]] {
  override val toString = s"{${p.mkString(",")}}"
}

object Trigger {
  def apply(t: Term) = new Trigger(t :: Nil)
  def apply(ts: Seq[Term]) = new Trigger(ts)

  def unapply(trigger: Trigger) = Some(trigger.p)
}

class Quantification private[terms] (val q: Quantifier,
                                     val vars: Seq[Var],
                                     val body: Term,
                                     val triggers: Seq[Trigger])
    extends BooleanTerm
       with commonnodes.StructuralEquality {

  lazy val autoTrigger: Quantification = {
    if (triggers.nonEmpty) {
      /* Triggers were given explicitly */
      this
    } else {
      val results = TriggerGenerator.generateTriggers(vars, body)

      if (results.nonEmpty) {
        val (generatedTriggers, extraVariables) = results(0)
        Quantification(q, vars ++ extraVariables, body, generatedTriggers)
      } else {
        /* TODO: Emit warning that no triggers were found */
        this
      }
    }
  }

  val equalityDefiningMembers = q :: vars :: body :: triggers :: Nil

  override val toString = s"$q ${vars.mkString(",")} :: $body"
}

object Quantification extends ((Quantifier, Seq[Var], Term, Seq[Trigger]) => Quantification) {
  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger]) =
    /* TODO: If we optimise away a quantifier, we cannot, for example, access
     *       autoTrigger on the returned object.
     */
    new Quantification(q, vars, tBody, triggers)
//    tBody match {
//    case True() | False() => tBody
//    case _ => new Quantification(q, vars, tBody, triggers)
//  }

  def unapply(q: Quantification) = Some((q.q, q.vars, q.body, q.triggers))
}

/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
		with commonnodes.Plus[Term] with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger

object Plus extends Function2[Term, Term, Term] {
	import predef.Zero

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
    with ForbiddenInTrigger

object Minus extends Function2[Term, Term, Term] {
	import predef.Zero

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
    with ForbiddenInTrigger

object Times extends Function2[Term, Term, Term] {
	import predef.{Zero, One}

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
		with commonnodes.Div[Term] with ForbiddenInTrigger

case class Mod(p0: Term, p1: Term) extends ArithmeticTerm
		with commonnodes.Mod[Term] with ForbiddenInTrigger

/* Boolean expression terms */

sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }

class Not(val p: Term) extends BooleanTerm
    with commonnodes.StructuralEqualityUnaryOp[Term] with ForbiddenInTrigger {

	override val op = "!"

	override val toString = p match {
		case eq: BuiltinEquals => eq.p0.toString + " != " + eq.p1.toString
		case _ => super.toString
	}
}

object Not extends (Term => Term) {
	def apply(e0: Term) = e0 match {
		case Not(e1) => e1
		case True() => False()
		case False() => True()
		case _ => new Not(e0)
	}

	def unapply(e: Not) = Some(e.p)
}

class Or(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Or[Term] with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger

/* TODO: Or should be (Term, Term) => BooleanTerm, but that require a
 *       Boolean(t: Term) wrapper, because e0/e1 may just be a Var.
 *       It would be sooooo handy to be able to work with Term[Sort], but
 *       that conflicts with using extractor objects to simplify terms,
 *       since extractor objects can't be type-parameterised.
 */
object Or extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (True(), _) | (_, True()) => True()
		case (False(), _) => e1
		case (_, False()) => e0
		case _ if e0 == e1 => e0
		case _ => new Or(e0, e1)
	}

	def unapply(e: Or) = Some((e.p0, e.p1))
}

class And(val ts: Seq[Term]) extends BooleanTerm
    with commonnodes.StructuralEquality with ForbiddenInTrigger {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  val equalityDefiningMembers = ts

  override lazy val toString = ts.mkString(" && ")
}

object And {
  def apply(ts: Term*) = createAnd(ts)
  def apply(ts: Set[Term]) = createAnd(ts.toSeq)

  @inline
  def createAnd(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case And(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == True())
    ts = ts.distinct

    ts match {
      case Seq() => True()
      case Seq(t) => t
      case _ => new And(ts)
    }
  }

	def unapply(e: And) = Some(e.ts)
}

class Implies(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Implies[Term] with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger

object Implies extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term): Term = (e0, e1) match {
		case (True(), _) => e1
		case (False(), _) => True()
		case (_, True()) => True()
		case (_, Implies(e10, e11)) => Implies(And(e0, e10), e11)
		case _ if e0 == e1 => True()
		case _ => new Implies(e0, e1)
	}

	def unapply(e: Implies) = Some((e.p0, e.p1))
}

class Iff(val p0: Term, val p1: Term) extends BooleanTerm
		with commonnodes.Iff[Term] with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger

object Iff extends Function2[Term, Term, Term] {
	def apply(e0: Term, e1: Term) = (e0, e1) match {
		case (True(), _) => e1
		case (_, True()) => e0
		case _ if e0 == e1 => True()
		case _ => new Iff(e0, e1)
	}

	def unapply(e: Iff) = Some((e.p0, e.p1))
}

class Ite(val t0: Term, val t1: Term, val t2: Term)
    extends Term
       with ForbiddenInTrigger
       with commonnodes.StructuralEquality {

	assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
			"Ite term Ite(%s, %s, %s) is not well-sorted: %s, %s, %s"
			.format(t0, t1, t2, t0.sort, t1.sort, t2.sort))


  val equalityDefiningMembers = t0 :: t1 :: t2 :: Nil
  val sort = t1.sort
  override val toString = "(%s ? %s : %s)".format(t0, t1, t2)
}

object Ite extends Function3[Term, Term, Term, Term] {
	def apply(e0: Term, e1: Term, e2: Term) = (e0, e1, e2) match {
    case _ if e1 == e2 => e1
    case (True(), _, _) => e1
    case (False(), _, _) => e2
    case (_, True(), False()) => e0
    case (_, False(), True()) => Not(e0)
		case _ => new Ite(e0, e1, e2)
	}

	def unapply(e: Ite) = Some((e.t0, e.t1, e.t2))
}

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

sealed trait Equals extends ComparisonTerm with commonnodes.Eq[Term]

object Equals extends ((Term, Term) => BooleanTerm) {
  def apply(e0: Term, e1: Term) = {
    assert(e0.sort == e1.sort,
           "Expected both operands to be of the same sort, but found %s (%s) and %s (%s)."
           .format(e0.sort, e0, e1.sort, e1))

    if (e0 == e1)
      True()
    else
      e0.sort match {
        case sorts.Perm => BuiltinEquals.forPerm(e0, e1)
        case _: sorts.Seq | _: sorts.Set | _: sorts.Multiset => new CustomEquals(e0, e1)
        case _ => new BuiltinEquals(e0, e1)
      }
  }

  def unapply(e: Equals) = Some((e.p0, e.p1))
}

/* Represents built-in equality, e.g., '=' in SMT-LIB */
class BuiltinEquals private[terms] (val p0: Term, val p1: Term) extends Equals
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger {
}

object BuiltinEquals {
  def forPerm(t1: Term, t2: Term) = (t1, t2) match {
    case (FullPerm(), NoPerm()) | (NoPerm(), FullPerm()) => False()
    case (NoPerm(), fp: FractionPerm) if fp.isDefinitelyPositive => False()
    case (fp: FractionPerm, NoPerm()) if fp.isDefinitelyPositive => False()
    case (FullPerm(), fp: FractionPerm) if fp.isLiteral => False()
    case (fp: FractionPerm, FullPerm()) if fp.isLiteral => False()
    case _ => new BuiltinEquals(t1, t2)
  }

  def unapply(e: BuiltinEquals) = Some((e.p0, e.p1))
}

/* Custom equality that (potentially) needs to be axiomatised. */
class CustomEquals private[terms] (val p0: Term, val p1: Term) extends Equals
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  def getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = Equals(args(0), args(1)).asInstanceOf[CustomEquals]
    /* The cast will raise an exception if the equality has been optimised away */
}

object CustomEquals {
  def unapply(e: CustomEquals) = Some((e.p0, e.p1))
}


class Less(val p0: Term, val p1: Term) extends ComparisonTerm
    with commonnodes.Less[Term] with commonnodes.StructuralEqualityBinaryOp[Term]
    with ForbiddenInTrigger {

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
    with ForbiddenInTrigger

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
    with ForbiddenInTrigger

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
    with ForbiddenInTrigger

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

sealed trait Permissions extends Term {
  val sort = sorts.Perm
}

case class NoPerm() extends Permissions { override val toString = "Z" }
case class FullPerm() extends Permissions { override val toString = "W" }
case class WildcardPerm(v: Var) extends Permissions { override val toString = v.toString }

class FractionPerm(val n: Term, val d: Term)
    extends Permissions
       with commonnodes.StructuralEquality {

  lazy val isDefinitelyPositive = literal match {
    case Some((i1, i2)) => 0 < i1 * i2
    case None => false
  }

  lazy val isLiteral = literal.nonEmpty

  lazy val literal = (n, d) match {
    case (IntLiteral(i1), IntLiteral(i2)) => Some((i1, i2))
    case _ => None
  }

  val equalityDefiningMembers = n :: d :: Nil
  override val toString = s"$n/$d"
}

object FractionPerm extends ((Term, Term) => Permissions) {
  def apply(n: Term, d: Term) =
    if (n == predef.Zero) NoPerm()
    else if (n == d) FullPerm()
    else new FractionPerm(n, d)

  def unapply(fp: FractionPerm) = Some((fp.n, fp.d))
}

case class IsValidPermVar(v: Var) extends BooleanTerm {
  override val toString = s"PVar($v)"
}

case class IsReadPermVar(v: Var, ub: Term) extends BooleanTerm {
  override val toString = s"RdVar($v, $ub)"
}

class PermTimes(val p0: Term, val p1: Term)
    extends Permissions
       with commonnodes.Times[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger

object PermTimes extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (FullPerm(), t) => t
    case (t, FullPerm()) => t
    case (NoPerm(), _) => NoPerm()
    case (_, NoPerm()) => NoPerm()
    case (_, _) => new PermTimes(t0, t1)
  }

  def unapply(pt: PermTimes) = Some((pt.p0, pt.p1))
}

class IntPermTimes(val p0: Term, val p1: Term)
    extends Permissions
       with commonnodes.Times[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger

object IntPermTimes extends ((Term, Term) => Term) {
  import predef.{Zero, One}

  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (Zero, t) => NoPerm()
    case (One, t) => t
    case (_, NoPerm()) => NoPerm()
    case (_, _) => new IntPermTimes(t0, t1)
  }

  def unapply(pt: IntPermTimes) = Some((pt.p0, pt.p1))
}

case class PermIntDiv(p0: Term, p1: Term)
    extends Permissions
       with commonnodes.Div[Term]
//    with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger {

  utils.assertSort(p1, "Second term", sorts.Int)
}

class PermPlus(val p0: Term, val p1: Term)
    extends Permissions
       with commonnodes.Plus[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger

object PermPlus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (NoPerm(), _) => t1
    case (_, NoPerm()) => t0
    case (FractionPerm(n1, d1), FractionPerm(n2, d2)) if d1 == d2 => FractionPerm(Plus(n1, n2), d1)
    case (PermMinus(t00, t01), _) if t01 == t1 => t00
    case (_, PermMinus(t10, t11)) if t11 == t0 => t10

    case (_, _) => new PermPlus(t0, t1)
  }

  def unapply(pp: PermPlus) = Some((pp.p0, pp.p1))
}

class PermMinus(val p0: Term, val p1: Term)
    extends Permissions
       with commonnodes.Minus[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger {

  override val toString = p1 match {
    case _: commonnodes.BinaryOp[_] => s"$p0 $op ($p1)"
    case _ => s"$p0 $op $p1"
  }
}

object PermMinus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (_, NoPerm()) => t0
    case (p0, p1) if p0 == p1 => NoPerm()
    case (p0, PermMinus(p1, p2)) if p0 == p1 => p2
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => new PermMinus(t0, t1)
  }

  def unapply(pm: PermMinus) = Some((pm.p0, pm.p1))
}

class PermLess(val p0: Term, val p1: Term)
    extends BooleanTerm
       with commonnodes.Less[Term]
       with commonnodes.StructuralEqualityBinaryOp[Term]
       with ForbiddenInTrigger {

  override val toString = "(%s) < (%s)".format(p0, p1)
}

object PermLess extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = {
    (t0, t1) match {
      case _ if t0 == t1 => False()
      case (NoPerm(), FullPerm()) => True()
      case (FullPerm(), _: WildcardPerm) => False()

      case (`t0`, Ite(tCond, tIf, tElse)) =>
        /* The pattern p0 < b ? p1 < p2 arises very often in the context of quantified permissions.
         * Pushing the comparisons into the ite allows further simplifications.
         */
        Ite(tCond, PermLess(t0, tIf), PermLess(t0, tElse))

      case _ => new PermLess(t0, t1)
    }
  }

  def unapply(pl: PermLess) = Some((pl.p0, pl.p1))
}

case class PermMin(p0: Term, p1: Term) extends Permissions
    with commonnodes.BinaryOp[Term]
    with PossibleBinaryOpTrigger[Term] {

  utils.assertSort(p0, "Permission 1st", sorts.Perm)
  utils.assertSort(p1, "Permission 2nd", sorts.Perm)

  override val toString = s"min ($p0, $p1)"

  def withArgs(args: Seq[Term]) = PermMin(args(0), args(1))
}

/* Functions */

case class Apply(func: Term, args: Seq[Term]) extends Term with PossibleTrigger {
  val funcSort = func.sort match {
    case a: sorts.Arrow => a
    case other => sys.error(s"Cannot apply $func of sort $other to $args")
  }

  val sort = funcSort.to

  override val toString = s"$func(${args.mkString(",")})"

  lazy val getArgs = func +: args
  def withArgs(args: Seq[Term]) = Apply(args.head, args.tail)
}

case class FApp(function: Function, snapshot: Term, tArgs: Seq[Term]) extends Term with PossibleTrigger {
  utils.assertSort(snapshot, "snapshot", sorts.Snap)

  val sort = function.sort.to

  lazy val limitedVersion = FApp(function.limitedVersion, snapshot, tArgs)

  override val toString = s"${function.id}(${tArgs.mkString(",")};$snapshot)"

  lazy val getArgs = snapshot +: tArgs
  def withArgs(args: Seq[Term]) = FApp(function, args.head, args.tail)
}

/* Sequences */

sealed trait SeqTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Seq
}

case class SeqRanged(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ with PossibleTrigger  {
  utils.assertSort(p0, "first operand", sorts.Int)
  utils.assertSort(p1, "second operand", sorts.Int)

  val elementsSort = sorts.Int
  val sort = sorts.Seq(elementsSort)

  override val toString = "[%s..%s]".format(p0, p1)

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqRanged(args(0), args(1))
}

case class SeqNil(elementsSort: Sort) extends SeqTerm with Literal {
  val sort = sorts.Seq(elementsSort)
  override val toString = "Nil"
}

case class SeqSingleton(p: Term) extends SeqTerm /* with UnaryOp[Term] */ with PossibleTrigger {
  val elementsSort = p.sort
  val sort = sorts.Seq(elementsSort)

  override val toString = "[" + p + "]"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = SeqSingleton(args(0))
}

class SeqAppend(val p0: Term, val p1: Term) extends SeqTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val op = "++"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqAppend(args(0), args(1))
}

object SeqAppend extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSeqSorts(t0, t1)
    new SeqAppend(t0, t1)
  }

  def unapply(sa: SeqAppend) = Some((sa.p0, sa.p1))
}

class SeqDrop(val p0: Term, val p1: Term) extends SeqTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val toString = p0 + "[" + p1 + ":]"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqDrop(args(0), args(1))
}

object SeqDrop extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqDrop(t0, t1)
  }

  def unapply(sd: SeqDrop) = Some((sd.p0, sd.p1))
}

class SeqTake(val p0: Term, val p1: Term) extends SeqTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val toString = p0 + "[:" + p1 + "]"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqTake(args(0), args(1))
}

object SeqTake extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqTake(t0, t1)
  }

  def unapply(st: SeqTake) = Some((st.p0, st.p1))
}

class SeqLength(val p: Term) extends Term
    with commonnodes.StructuralEqualityUnaryOp[Term]
    with PossibleTrigger {

  val sort = sorts.Int
  override val toString = "|" + p + "|"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = SeqLength(args(0))
}

object SeqLength {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Seq", _.isInstanceOf[sorts.Seq])
    new SeqLength(t)
  }

  def unapply(sl: SeqLength) = Some(sl.p)
}

class SeqAt(val p0: Term, val p1: Term) extends Term
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val sort = p0.sort.asInstanceOf[sorts.Seq].elementsSort

  override val toString = p0 + "[" + p1 + "]"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqAt(args(0), args(1))
}

object SeqAt extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqAt(t0, t1)
  }

  def unapply(sa: SeqAt) = Some((sa.p0, sa.p1))
}

class SeqIn(val p0: Term, val p1: Term) extends BooleanTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  override val toString = "%s in %s".format(p1, p0)

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SeqIn(args(0), args(1))
}

object SeqIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    new SeqIn(t0, t1)
  }

  def unapply(si: SeqIn) = Some((si.p0, si.p1))
}

class SeqUpdate(val t0: Term, val t1: Term, val t2: Term)
    extends SeqTerm
       with commonnodes.StructuralEquality
       with PossibleTrigger {

  val sort = t0.sort.asInstanceOf[sorts.Seq]
  val elementsSort = sort.elementsSort
  val equalityDefiningMembers = t0 :: t1 :: t2 :: Nil
  override val toString = s"$t0[$t1] := $t2"

  lazy val getArgs = t0 :: t1 :: t2 :: Nil
  def withArgs(args: Seq[Term]) = SeqUpdate(args(0), args(1), args(2))
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

sealed trait BinarySetOp extends SetTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleBinaryOpTrigger[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)
}

case class EmptySet(elementsSort: Sort) extends SetTerm with Literal {
  val sort = sorts.Set(elementsSort)
  override val toString = "Ø"
}

case class SingletonSet(p: Term) extends SetTerm /* with UnaryOp[Term] */ with PossibleTrigger {
  val elementsSort = p.sort
  val sort = sorts.Set(elementsSort)

  override val toString = "{" + p + "}"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = SingletonSet(args(0))
}

class SetAdd(val p0: Term, val p1: Term) extends SetTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)

  override val op = "+"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SetAdd(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = SetUnion(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = SetIntersection(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = SetSubset(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = SetDisjoint(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = SetDifference(args(0), args(1))
}

object SetDifference extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSetSorts(t0, t1)
    new SetDifference(t0, t1)
  }

  def unapply(sd: SetDifference) = Some((sd.p0, sd.p1))
}

class SetIn(val p0: Term, val p1: Term) extends BooleanTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  override val op = "in"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = SetIn(args(0), args(1))
}

object SetIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t1, "second operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Set].elementsSort)

    new SetIn(t0, t1)
  }

  def unapply(si: SetIn) = Some((si.p0, si.p1))
}

class SetCardinality(val p: Term) extends Term
    with commonnodes.StructuralEqualityUnaryOp[Term]
    with PossibleTrigger {

  val sort = sorts.Int
  override val toString = "|" + p + "|"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = SetCardinality(args(0))
}

object SetCardinality extends (Term => SetCardinality) {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Set", _.isInstanceOf[sorts.Set])
    new SetCardinality(t)
  }

  def unapply(sc: SetCardinality) = Some(sc.p)
}

/* Multisets */

sealed trait MultisetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Multiset
}

sealed trait BinaryMultisetOp extends MultisetTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleBinaryOpTrigger[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

case class EmptyMultiset(elementsSort: Sort) extends MultisetTerm with Literal {
  val sort = sorts.Multiset(elementsSort)
  override val toString = "Ø"
}

case class SingletonMultiset(p: Term) extends MultisetTerm /* with UnaryOp[Term] */ with PossibleTrigger {
  val elementsSort = p.sort
  val sort = sorts.Multiset(elementsSort)

  override val toString = "{" + p + "}"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = SingletonMultiset(args(0))
}

class MultisetAdd(val p0: Term, val p1: Term) extends MultisetTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)

  override val op = "+"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = MultisetAdd(args(0), args(1))
}

object MultisetAdd extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetAdd(t0, t1)
  }

  def unapply(ma: MultisetAdd) = Some((ma.p0, ma.p1))
}

class MultisetUnion(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∪"

  def withArgs(args: Seq[Term]) = MultisetUnion(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = MultisetIntersection(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = MultisetSubset(args(0), args(1))
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

  def withArgs(args: Seq[Term]) = MultisetDifference(args(0), args(1))
}

object MultisetDifference extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameMultisetSorts(t0, t1)
    new MultisetDifference(t0, t1)
  }

  def unapply(md: MultisetDifference) = Some((md.p0, md.p1))
}

class MultisetIn(val p0: Term, val p1: Term) extends BooleanTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  override val op = "∈"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = MultisetIn(args(0), args(1))
}

object MultisetIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSort(t1, "second operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetIn(t0, t1)
  }

  def unapply(mi: MultisetIn) = Some((mi.p0, mi.p1))
}

class MultisetCardinality(val p: Term) extends Term
    with commonnodes.StructuralEqualityUnaryOp[Term]
    with PossibleTrigger {

  val sort = sorts.Int
  override val toString = "|" + p + "|"

  lazy val getArgs = p :: Nil
  def withArgs(args: Seq[Term]) = MultisetCardinality(args(0))
}

object MultisetCardinality extends (Term => MultisetCardinality) {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Multiset", _.isInstanceOf[sorts.Multiset])
    new MultisetCardinality(t)
  }

  def unapply(mc: MultisetCardinality) = Some(mc.p)
}

class MultisetCount(val p0: Term, val p1: Term) extends Term
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  val sort = sorts.Int
  override val toString = s"cnt($p0,$p1)"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = MultisetCount(args(0), args(1))
}

object MultisetCount extends {
  def apply(e:Term, t:Term) = {
    utils.assertSort(t, "second operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(e, "first operand", t.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetCount(e,t)
  }

  def unapply(mc:MultisetCount) = Some((mc.p0, mc.p1))
}

/* Domains */

case class DomainFApp(function: Function, tArgs: Seq[Term]) extends Term with PossibleTrigger {
  val sort = function.sort.to
  override val toString = function.id + tArgs.mkString("(", ", ", ")")

  lazy val getArgs = tArgs
  def withArgs(args: Seq[Term]) = DomainFApp(function, args)
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

class Combine(val p0: Term, val p1: Term) extends SnapshotTerm
    with commonnodes.StructuralEqualityBinaryOp[Term]
    with PossibleTrigger {

  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)

  override val toString = s"($p0, $p1)"

  lazy val getArgs = p0 :: p1 :: Nil
  def withArgs(args: Seq[Term]) = Combine(args(0), args(1))
}

object Combine {
  def apply(t0: Term, t1: Term) = new Combine(t0.convert(sorts.Snap), t1.convert(sorts.Snap))

  def unapply(c: Combine) = Some((c.p0, c.p1))
}

case class First(t: Term) extends SnapshotTerm with PossibleTrigger {
  utils.assertSort(t, "term", sorts.Snap)

  lazy val getArgs = t :: Nil
  def withArgs(args: Seq[Term]) = First(args(0))
}

case class Second(t: Term) extends SnapshotTerm with PossibleTrigger {
  utils.assertSort(t, "term", sorts.Snap)

  lazy val getArgs = t :: Nil
  def withArgs(args: Seq[Term]) = Second(args(0))
}

/* Sort wrappers */

/* Note: Sort wrappers should probably not be used as (outermost) triggers
 * because they are optimised away if wrappee `t` already has sort `to`.
 */
class SortWrapper(val t: Term, val to: Sort)
    extends Term
       with commonnodes.StructuralEquality {

  assert((t.sort == sorts.Snap || to == sorts.Snap) && t.sort != to,
         s"Unexpected sort wrapping of $t from ${t.sort} to $to")

  val equalityDefiningMembers = t :: to :: Nil
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

/* Trigger-related terms */

sealed trait PossibleTrigger extends Term with GenericTriggerGenerator.PossibleTrigger[Term, PossibleTrigger] {
  val asManifestation = this
  /* Returning this assumes that the possible trigger is always the trigger
   * term itself. This is not the case, for example, on Silver's side, where
   * an old-expression itself is not the trigger, but where the expression
   * nested in 'old' is the trigger.
   */
}

sealed trait PossibleBinaryOpTrigger[T <: Term] extends PossibleTrigger { self: commonnodes.BinaryOp[T] =>
  lazy val getArgs = p0 :: p1 :: Nil
}

sealed trait ForbiddenInTrigger extends Term with GenericTriggerGenerator.ForbiddenInTrigger[Sort] {
  lazy val typ = sort
}

/* Other terms */

class Distinct(val ts: Set[Term]) extends BooleanTerm with commonnodes.StructuralEquality {
  assert(ts.nonEmpty, "Distinct requires at least term.")

  val equalityDefiningMembers = ts :: Nil
  override val toString = s"Distinct($ts)"
}

object Distinct {
  def apply(ts: Set[Term]): Term =
    if (ts.nonEmpty) new Distinct(ts)
    else True()

  def unapply(d: Distinct) = Some(d.ts)
}

/* Predefined terms */

object predef {
  val `?s` = Var("s@$", sorts.Snap) // with SnapshotTerm

  val Zero = IntLiteral(0)
  val One = IntLiteral(1)
}

/* Convenience functions */

object perms {
  def IsNonNegative(p: Term) =
    Or(p === NoPerm(), IsPositive(p))
      /* All basic static simplifications should be covered by Equals,
       * IsPositive and or
       */

  def IsPositive(p: Term) = p match {
    case _: NoPerm => False()
    case _: FullPerm | _: WildcardPerm => True()
    case fp: FractionPerm if fp.isDefinitelyPositive => True()
    case _ => PermLess(NoPerm(), p)
  }

  def IsAsPermissive(p1: Term, p2: Term) = Or(p1 === p2, PermLess(p2, p1))

  def IsNoAccess(p: Term) = p match {
    case _: NoPerm => True()
    case  _: PermPlus | PermMinus(_, _: WildcardPerm) => False()
      /* ATTENTION: This is only sound if both plus operands and the left minus operand are positive! */
    case _ => Or(p === NoPerm(), PermLess(p, NoPerm()))
  }
}

/* Utility functions */

object utils {
  def BigOr(it: Iterable[Term], f: Term => Term = t => t): Term =
    silicon.utils.mapReduceLeft(it, f, Or, True())

  def BigPermSum(it: Iterable[Term], f: Term => Term = t => t): Term =
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
