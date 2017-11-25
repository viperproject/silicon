/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state.terms

import scala.reflect.ClassTag
import viper.silver.ast.utility.Visitor
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Map, Stack, state, toMap}
import viper.silicon.state.{Identifier, MagicWandChunk}

sealed trait Node

sealed trait Symbol extends Node {
  def id: Identifier
}

/*
 * Sorts
 */

sealed trait Sort extends Symbol

object sorts {
  object Snap extends Sort { val id = Identifier("Snap"); override val toString = id.toString }
  object Int  extends Sort { val id = Identifier("Int");  override val toString = id.toString }
  object Bool extends Sort { val id = Identifier("Bool"); override val toString = id.toString }
  object Ref  extends Sort { val id = Identifier("Ref");  override val toString = id.toString }
  object Perm extends Sort { val id = Identifier("Perm"); override val toString = id.toString }
  object Unit extends Sort { val id = Identifier("()");   override val toString = id.toString }

  case class Seq(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Seq[$elementsSort]")
    override val toString = id.toString
  }

  case class Set(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Set[$elementsSort]")
    override val toString = id.toString
  }

  case class Multiset(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Multiset[$elementsSort]")
    override val toString = id.toString
  }

  case class UserSort(id: Identifier) extends Sort {
    override val toString = id.toString
  }

  case class FieldValueFunction(codomainSort: Sort) extends Sort {
    val id = Identifier(s"FVF[$codomainSort]")
    override val toString = id.toString
  }

  case class PredicateSnapFunction(codomainSort: Sort) extends Sort {
    val id = Identifier(s"PSF[$codomainSort]")
    override val toString = id.toString
  }

}

/*
 * Declarations
 */

sealed trait Decl extends Node

case class SortDecl(sort: Sort) extends Decl
case class FunctionDecl(func: Function) extends Decl
case class SortWrapperDecl(from: Sort, to: Sort) extends Decl
case class MacroDecl(id: Identifier, args: Seq[Var], body: Term) extends Decl

object ConstDecl extends (Var => Decl) { /* TODO: Inconsistent naming - Const vs Var */
  def apply(v: Var) = FunctionDecl(v)
}

/*
 * Applicables and Applications
 */

sealed trait Applicable extends Symbol {
  def argSorts: Seq[Sort]
  def resultSort: Sort
}

sealed trait Application[A <: Applicable] extends Term {
  def applicable: A
  def args: Seq[Term]
}

sealed trait Function extends Applicable

object Function {
  def unapply(fun: Function): Option[(Identifier, Seq[Sort], Sort)] =
    Some((fun.id, fun.argSorts, fun.resultSort))
}

/* RFC: [18-12-2015 Malte] An alternative to using different sub-classes of Function (e.g.
 *      Fun, HeapDepFun, ...) would be to use a single Fun class that as an additional property
 *      (i.e. field) that indicates the kind of
 */

trait GenericFunction[F <: Function] extends Function with StructuralEquality {
  val equalityDefiningMembers = id +: argSorts :+ resultSort

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort): F

  override val toString =
    if (argSorts.isEmpty) s"$id: $resultSort"
    else s"$id: ${argSorts.mkString(" x ")} -> $resultSort"
}

trait GenericFunctionCompanion[F <: Function] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort): F

  def apply(id: Identifier, argSort: Sort, resultSort: Sort): F =
    apply(id, Seq(argSort), resultSort)

  def unapply(fun: F): Option[(Identifier, Seq[Sort], Sort)] =
    Some((fun.id, fun.argSorts, fun.resultSort))
}

class Fun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends GenericFunction[Fun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    Fun(id, argSorts, resultSort)
}

object Fun extends ((Identifier, Seq[Sort], Sort) => Fun) with GenericFunctionCompanion[Fun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = new Fun(id, argSorts, resultSort)
}

/* TODO: [18-12-2015 Malte] Since heap-dependent functions are represented by a separate class,
 *       it might make sense to add methods isLimited/isStateless and transformers
 *       toLimited/toStateless, and to remove the corresponding methods from the FunctionSupporter
 *       object.
 */
class HeapDepFun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends GenericFunction[HeapDepFun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    HeapDepFun(id, argSorts, resultSort)
}

object HeapDepFun extends ((Identifier, Seq[Sort], Sort) => HeapDepFun) with GenericFunctionCompanion[HeapDepFun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = new HeapDepFun(id, argSorts, resultSort)
}

class DomainFun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends GenericFunction[DomainFun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    DomainFun(id, argSorts, resultSort)
}

object DomainFun extends ((Identifier, Seq[Sort], Sort) => DomainFun) with GenericFunctionCompanion[DomainFun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = new DomainFun(id, argSorts, resultSort)
}

case class Macro(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) extends Applicable

case class Var(id: Identifier, sort: Sort) extends Function with Application[Var] {
  val applicable: Var = this
  val args: Seq[Term] = Seq.empty
  val argSorts: Seq[Sort] = Seq(sorts.Unit)
  val resultSort: Sort = sort

  override val toString = id.toString
}

class App(val applicable: Applicable, val args: Seq[Term])
    extends Application[Applicable]
       with StructuralEquality {
       /*with PossibleTrigger*/

  utils.assertExpectedSorts(applicable, args)

  val sort: Sort = applicable.resultSort
  val equalityDefiningMembers = applicable +: args
  def copy(applicable: Applicable = applicable, args: Seq[Term] = args) = App(applicable, args)

  override val toString =
    if (args.isEmpty) applicable.id.toString
    else s"${applicable.id}${args.mkString("(", ", ", ")")}"
}

object App extends ((Applicable, Seq[Term]) => App) {
  def apply(applicable: Applicable, args: Seq[Term]) = new App(applicable, args)
  def apply(applicable: Applicable, arg: Term) = new App(applicable, Seq(arg))
  def unapply(app: App) = Some((app.applicable, app.args))
}

/*
 * Terms
 */

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

sealed trait Term extends Node {
  def sort: Sort

  def ===(t: Term): Term = Equals(this, t)
  def !==(t: Term): Term = Not(Equals(this, t))

  def convert(to: Sort): Term = SortWrapper(this, to)

  lazy val subterms = state.utils.subterms(this)

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[Term, Any]) =
    Visitor.visit(this, state.utils.subterms)(f)

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: Term => Boolean) =
    Visitor.visitOpt(this, state.utils.subterms)(f)

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

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[Term, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[Visitor.find()]] */
  def find[R](f: PartialFunction[Term, R]): Option[R] =
    Visitor.find(this, state.utils.subterms)(f)

  /** @see [[state.utils.transform()]] */
  def transform(pre: PartialFunction[Term, Term] = PartialFunction.empty)
               (recursive: Term => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[Term, Term] = PartialFunction.empty)
               : this.type =  state.utils.transform[this.type](this, pre)(recursive, post)

  def replace(original: Term, replacement: Term): Term =
    if (original == replacement)
      this
    else
      this.transform{case `original` => replacement}()

  def replace[T <: Term : ClassTag](replacements: Map[T, Term]): Term =
    if (replacements.isEmpty)
      this
    else
      this.transform{case t: T if replacements.contains(t) => replacements(t)}()

  def replace(originals: Seq[Term], replacements: Seq[Term]): Term = {
    //    assert(originals.length == replacements.length)

    if (originals.isEmpty)
      this
    else
      this.replace(toMap(originals.zip(replacements)))
  }

  def contains(t: Term): Boolean = this.existsDefined{case `t` =>}

  lazy val freeVariables =
    this.reduceTree((t: Term, freeVarsChildren: Seq[Set[Var]]) => {
      val freeVars: InsertionOrderedSet[Var] = InsertionOrderedSet(freeVarsChildren.flatten)

      t match {
        case q: Quantification =>
          freeVars filterNot q.vars.contains
        case l: Let =>
          val lvars = l.bindings.keySet
          freeVars diff lvars
        case v: Var =>
          freeVars + v
        case _ =>
          freeVars
      }
    })

  lazy val topLevelConjuncts: Seq[Term] = {
    this match {
      case and: And => and.subterms flatMap (_.topLevelConjuncts)
      case other => Vector(other)
    }
  }
}

trait UnaryOp[E] {
  def op: String = getClass.getSimpleName.stripSuffix("$") + ":"
  /* If UnaryOp is extended by a case-class then getSimpleName returns
   * the class name suffixed with a dollar sign.
   */
  def p: E

  override def toString = op + p
}

trait BinaryOp[E] {
  def op: String = getClass.getSimpleName.stripSuffix("$")
  def p0: E
  def p1: E

  override def toString = s"$p0 $op $p1"
}

trait StructuralEqualityUnaryOp[E] extends UnaryOp[E] {
  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case uop: UnaryOp[_] if uop.getClass.eq(this.getClass) => p == uop.p
      case _ => false
    })

  override def hashCode(): Int = p.hashCode
}

trait StructuralEqualityBinaryOp[E] extends BinaryOp[E] {
  override def equals(other: Any) =
    this.eq(other.asInstanceOf[AnyRef]) || (other match {
      case bop: BinaryOp[_] if bop.getClass.eq(this.getClass) =>
        /* getClass identity is checked in order to prohibit that different
         * subtypes of BinaryOp are considered equal.
         */
        p0 == bop.p0 && p1 == bop.p1

      case _ => false
    })

  override def hashCode(): Int = p0.hashCode() * p1.hashCode()
}

trait StructuralEquality { self: AnyRef =>
  val equalityDefiningMembers: Seq[Any]

  override val hashCode = viper.silver.utility.Common.generateHashCode(equalityDefiningMembers)

  override def equals(other: Any) = (
    this.eq(other.asInstanceOf[AnyRef])
      || (other match {
      case se: StructuralEquality if this.getClass.eq(se.getClass) =>
        equalityDefiningMembers == se.equalityDefiningMembers
      case _ => false
    }))
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

case object Forall extends Quantifier {
  def apply(qvar: Var, tBody: Term, trigger: Trigger): Quantification =
    apply(qvar, tBody, trigger, "")

  def apply(qvar: Var, tBody: Term, trigger: Trigger, name: String) =
    Quantification(Forall, qvar :: Nil, tBody, trigger :: Nil, name)

  def apply(qvar: Var, tBody: Term, trigger: Trigger, name: String, isGlobal: Boolean) =
    Quantification(Forall, qvar :: Nil, tBody, trigger :: Nil, name, isGlobal)

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(qvar, tBody, triggers, "")

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger], name: String) =
    Quantification(Forall, qvar :: Nil, tBody, triggers, name)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger): Quantification =
    apply(qvars, tBody, trigger, "")

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger, name: String) =
    Quantification(Forall, qvars, tBody, trigger :: Nil, name)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger, name: String, isGlobal: Boolean) =
    Quantification(Forall, qvars, tBody, trigger :: Nil, name, isGlobal)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(qvars, tBody, triggers, "")

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String) =
    Quantification(Forall, qvars, tBody, triggers, name)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String, isGlobal: Boolean) =
    Quantification(Forall, qvars, tBody, triggers, name, isGlobal)

  def unapply(q: Quantification): Option[(Seq[Var], Term, Seq[Trigger], String, Boolean)] =
    Some(q.vars, q.body, q.triggers, q.name, q.isGlobal)

  override val toString = "QA"
}

object Exists extends Quantifier {
  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvar :: Nil, tBody, triggers)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvars, tBody, triggers)

  def apply(qvars: Iterable[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvars.toSeq, tBody, triggers)

  override val toString = "QE"
}

class Quantification private[terms] (val q: Quantifier, /* TODO: Rename */
                                     val vars: Seq[Var],
                                     val body: Term,
                                     val triggers: Seq[Trigger],
                                     val name: String,
                                     val isGlobal: Boolean)
    extends BooleanTerm
       with StructuralEquality {

  val equalityDefiningMembers = q :: vars :: body :: triggers :: Nil

  def copy(q: Quantifier = q,
           vars: Seq[Var] = vars,
           body: Term = body,
           triggers: Seq[Trigger] = triggers,
           name: String = name,
           isGlobal: Boolean = isGlobal) = {

    Quantification(q, vars, body, triggers, name, isGlobal)
  }

  lazy val stringRepresentation = s"$q ${vars.mkString(",")} :: $body"
  lazy val stringRepresentationWithTriggers = s"$q ${vars.mkString(",")} :: ${triggers.mkString(",")} $body"

  override lazy val toString = stringRepresentation

  def toString(withTriggers: Boolean = false) =
    if (withTriggers) stringRepresentationWithTriggers
    else stringRepresentation
}

object Quantification
    extends ((Quantifier, Seq[Var], Term, Seq[Trigger], String, Boolean) => Quantification) {

  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(q, vars, tBody, triggers, "")

  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String)
           : Quantification = {

    apply(q, vars, tBody, triggers, "", false)
  }

  def apply(q: Quantifier,
            vars: Seq[Var],
            tBody: Term,
            triggers: Seq[Trigger],
            name: String,
            isGlobal: Boolean)
           : Quantification = {
//    assert(vars.distinct.length == vars.length, s"Found duplicate vars: $vars")
//    assert(triggers.distinct.length == triggers.length, s"Found duplicate triggers: $triggers")

    /* TODO: If we optimise away a quantifier, we cannot, for example, access
     *       autoTrigger on the returned object.
     */
    new Quantification(q, vars, tBody, triggers, name, isGlobal)
//    tBody match {
//    case True() | False() => tBody
//    case _ => new Quantification(q, vars, tBody, triggers)
//  }
  }

  def unapply(q: Quantification)
             : Option[(Quantifier, Seq[Var], Term, Seq[Trigger], String, Boolean)] = {

    Some((q.q, q.vars, q.body, q.triggers, q.name, q.isGlobal))
  }
}

/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
    with BinaryOp[Term] with StructuralEqualityBinaryOp[Term] {

  override val op = "+"
}

object Plus extends ((Term, Term) => Term) {
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
    with BinaryOp[Term] with StructuralEqualityBinaryOp[Term] {

  override val op = "-"
}

object Minus extends ((Term, Term) => Term) {
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
    with BinaryOp[Term] with StructuralEqualityBinaryOp[Term] {

  override val op = "*"
}

object Times extends ((Term, Term) => Term) {
  import predef.{Zero, One}

  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (_, Zero) => Zero
    case (Zero, _) => Zero
    case (t0, One) => t0
    case (One, t1) => t1
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 * n1)
    case _ => new Times(e0, e1)
  }

  def unapply(t: Times) = Some((t.p0, t.p1))
}

case class Div(p0: Term, p1: Term) extends ArithmeticTerm
    with BinaryOp[Term] {

  override val op = "/"
}

case class Mod(p0: Term, p1: Term) extends ArithmeticTerm
    with BinaryOp[Term] {

  override val op = "%"
}

/* Boolean expression terms */

sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }

class Not(val p: Term) extends BooleanTerm
    with StructuralEqualityUnaryOp[Term] {

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

class Or(val ts: Seq[Term]) extends BooleanTerm
    with StructuralEquality {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  val equalityDefiningMembers = ts

  override lazy val toString = ts.mkString(" || ")
}

/* TODO: Or should be (Term, Term) => BooleanTerm, but that would require
 *       a Boolean(t: Term) wrapper, because e0/e1 may just be a Var.
 *       It would be sooooo handy to be able to work with Term[Sort], but
 *       that conflicts with using extractor objects to simplify terms,
 *       since extractor objects can't be type-parametrised.
 */
object Or extends (Iterable[Term] => Term) {
  def apply(ts: Term*) = createOr(ts)
  def apply(ts: Iterable[Term]) = createOr(ts.toSeq)

  //  def apply(e0: Term, e1: Term) = (e0, e1) match {
  //    case (True(), _) | (_, True()) => True()
  //    case (False(), _) => e1
  //    case (_, False()) => e0
  //    case _ if e0 == e1 => e0
  //    case _ => new Or(e0, e1)
  //  }

  @inline
  def createOr(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case Or(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == False())
    ts = ts.distinct

    ts match {
      case Seq() => False()
      case Seq(t) => t
      case _ => new Or(ts)
    }
  }

  def unapply(e: Or) = Some(e.ts)
}

class And(val ts: Seq[Term]) extends BooleanTerm
    with StructuralEquality {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  val equalityDefiningMembers = ts

  override lazy val toString = ts.mkString(" && ")
}

object And extends (Iterable[Term] => Term) {
  def apply(ts: Term*) = createAnd(ts)
  def apply(ts: Iterable[Term]) = createAnd(ts.toSeq)

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
    with StructuralEqualityBinaryOp[Term] {

  override val op = "==>"
}

object Implies extends ((Term, Term) => Term) {
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
    with StructuralEqualityBinaryOp[Term] {

  override val op = "<==>"
}

object Iff extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (True(), _) => e1
    case (_, True()) => e0
    case _ if e0 == e1 => True()
    case _ => new Iff(e0, e1)
  }

  def unapply(e: Iff) = Some((e.p0, e.p1))
}

class Ite(val t0: Term, val t1: Term, val t2: Term)
    extends Term with StructuralEquality {

  assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
         s"Ite term Ite($t0, $t1, $t2) is not well-sorted: ${t0.sort}, ${t1.sort}, ${t2.sort}")

  val equalityDefiningMembers = t0 :: t1 :: t2 :: Nil
  val sort = t1.sort
  override val toString = s"($t0 ? $t1 : $t2)"
}

object Ite extends ((Term, Term, Term) => Term) {
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

sealed trait Equals extends ComparisonTerm with BinaryOp[Term] { override val op = "==" }

object Equals extends ((Term, Term) => BooleanTerm) {
  def apply(e0: Term, e1: Term) = {
    assert(e0.sort == e1.sort,
           s"Expected both operands to be of the same sort, but found ${e0.sort} ($e0) and ${e1.sort} ($e1).")

    if (e0 == e1)
      True()
    else
      e0.sort match {
        case sorts.Snap =>
          (e0, e1) match {
            case (sw1: SortWrapper, sw2: SortWrapper) if sw1.t.sort != sw2.t.sort =>
              assert(false, s"Equality '(Snap) $e0 == (Snap) $e1' is not allowed")
            case (_: Combine, _: SortWrapper) =>
              assert(false, s"Equality '$e0 == (Snap) $e1' is not allowed")
            case (_: SortWrapper, _: Combine) =>
              assert(false, s"Equality '(Snap) $e0 == $e1' is not allowed")
            case _ => /* Ok */
          }

          new BuiltinEquals(e0, e1)

        case _: sorts.Seq | _: sorts.Set | _: sorts.Multiset => new CustomEquals(e0, e1)
        case _ => new BuiltinEquals(e0, e1)
      }
  }

  def unapply(e: Equals) = Some((e.p0, e.p1))
}

/* Represents built-in equality, e.g., '=' in SMT-LIB */
class BuiltinEquals private[terms] (val p0: Term, val p1: Term) extends Equals
    with StructuralEqualityBinaryOp[Term]

object BuiltinEquals extends ((Term, Term) => BooleanTerm) {
  def apply(t1: Term, t2: Term) = (t1, t2) match {
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal == p1.literal) True() else False()
    case _ => new BuiltinEquals(t1, t2)
  }

  def unapply(e: BuiltinEquals) = Some((e.p0, e.p1))
}

/* Custom equality that (potentially) needs to be axiomatised. */
class CustomEquals private[terms] (val p0: Term, val p1: Term) extends Equals
    with StructuralEqualityBinaryOp[Term] {

  override val op = "==="
}

object CustomEquals extends ((Term, Term) => BooleanTerm) {
  def apply(t1: Term, t2: Term) = new CustomEquals(t1, t2)
  def unapply(e: CustomEquals) = Some((e.p0, e.p1))
}

class Less(val p0: Term, val p1: Term) extends ComparisonTerm
    with StructuralEqualityBinaryOp[Term] {

  assert(p0.sort == p1.sort,
         s"Expected both operands to be of the same sort, but found ${p0.sort} ($p0) and ${p1.sort} ($p1).")

  override val op = "<"
}

object Less extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True() else False()
    case (t0, t1) if t0 == t1 => False()
    case _ => new Less(e0, e1)
  }

  def unapply(e: Less) = Some((e.p0, e.p1))
}

class AtMost(val p0: Term, val p1: Term) extends ComparisonTerm
    with StructuralEqualityBinaryOp[Term] {

  override val op = "<="
}

object AtMost extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True() else False()
    case (t0, t1) if t0 == t1 => True()
    case _ => new AtMost(e0, e1)
  }

  def unapply(e: AtMost) = Some((e.p0, e.p1))
}

class Greater(val p0: Term, val p1: Term) extends ComparisonTerm
    with StructuralEqualityBinaryOp[Term] {

  override val op = ">"
}

object Greater extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True() else False()
    case (t0, t1) if t0 == t1 => False()
    case _ => new Greater(e0, e1)
  }

  def unapply(e: Greater) = Some((e.p0, e.p1))
}

class AtLeast(val p0: Term, val p1: Term) extends ComparisonTerm
    with StructuralEqualityBinaryOp[Term] {

  override val op = ">="
}

object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True() else False()
    case (t0, t1) if t0 == t1 => True()
    case _ => new AtLeast(e0, e1)
  }

  def unapply(e: AtLeast) = Some((e.p0, e.p1))
}

/*
  Helper class for permissions
 */

final class Rational(n: BigInt, d: BigInt) extends Ordered[Rational] {
  require(d != 0, "Denominator of Rational must not be 0.")

  private val g = n.gcd(d)
  val numerator: BigInt = n / g * d.signum
  val denominator: BigInt = d.abs / g

  def +(that: Rational): Rational = {
    val newNum = this.numerator * that.denominator + that.numerator * this.denominator
    val newDen = this.denominator * that.denominator
    Rational(newNum, newDen)
  }
  def -(that: Rational): Rational = this + (-that)
  def unary_- = Rational(-numerator, denominator)
  def abs = Rational(numerator.abs, denominator)
  def signum = Rational(numerator.signum, 1)

  def *(that: Rational): Rational = Rational(this.numerator * that.numerator, this.denominator * that.denominator)
  def /(that: Rational): Rational = this * that.inverse
  def inverse = Rational(denominator, numerator)

  def compare(that: Rational) = (this.numerator * that.denominator - that.numerator * this.denominator).signum

  override def equals(obj: Any) = obj match {
    case that: Rational => this.numerator == that.numerator && this.denominator == that.denominator
    case _ => false
  }

  override def toString = s"$numerator/$denominator"
}

object Rational extends ((BigInt, BigInt) => Rational) {
  val zero = Rational(0, 1)
  val one = Rational(1, 1)

  def apply(numer: BigInt, denom: BigInt) = new Rational(numer, denom)
  def unapply(r: Rational) = Some(r.numerator, r.denominator)
}

/*
 * Permissions
 */

sealed trait Permissions extends Term {
  val sort = sorts.Perm
}

sealed abstract class PermLiteral(val literal: Rational) extends Permissions

case class NoPerm() extends PermLiteral(Rational.zero) { override val toString = "Z" }
case class FullPerm() extends PermLiteral(Rational.one) { override val toString = "W" }

class FractionPermLiteral(r: Rational) extends PermLiteral(r) {
  override def equals(obj: Any) = obj match {
    case p: FractionPermLiteral => literal == p.literal
    case _ => false
  }
  override val toString = literal.toString
}

object FractionPermLiteral extends (Rational => Permissions) {
  def apply(r: Rational) = r match {
    case Rational(n, _) if n == 0 => NoPerm()
    case Rational(n, d) if n == d => FullPerm()
    case _ => new FractionPermLiteral(r)
  }

  def unapply(t: FractionPermLiteral) = Some(t.literal)
}

class FractionPerm(val n: Term, val d: Term)
    extends Permissions
       with StructuralEquality {

  val equalityDefiningMembers = n :: d :: Nil
  override val toString = s"$n/$d"
}

object FractionPerm extends ((Term, Term) => Permissions) {
  def apply(n: Term, d: Term) = (n, d) match {
    case (IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => FractionPermLiteral(Rational(i1, i2))
    case _ => new FractionPerm(n, d)
  }

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
       with StructuralEqualityBinaryOp[Term] {

  override val op = "*"
}

object PermTimes extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (FullPerm(), t) => t
    case (t, FullPerm()) => t
    case (NoPerm(), _) => NoPerm()
    case (_, NoPerm()) => NoPerm()
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal * p1.literal)
    case (_, _) => new PermTimes(t0, t1)
  }

  def unapply(pt: PermTimes) = Some((pt.p0, pt.p1))
}

class IntPermTimes(val p0: Term, val p1: Term)
    extends Permissions
       with BinaryOp[Term]
       with StructuralEqualityBinaryOp[Term] {

  override val op = "*"
}

object IntPermTimes extends ((Term, Term) => Term) {
  import predef.{Zero, One}

  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (Zero, _) => NoPerm()
    case (One, t) => t
    case (_, NoPerm()) => NoPerm()
    case (IntLiteral(i), p: PermLiteral) => FractionPermLiteral(Rational(i, 1) * p.literal)
    case (_, _) => new IntPermTimes(t0, t1)
  }

  def unapply(pt: IntPermTimes) = Some((pt.p0, pt.p1))
}

class PermIntDiv(val p0: Term, val p1: Term)
    extends Permissions
       with BinaryOp[Term]
       with StructuralEqualityBinaryOp[Term] {

  utils.assertSort(p1, "Second term", sorts.Int)

  override val op = "/"
}

object PermIntDiv extends ((Term, Term) => Term) {
  import predef.One

  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (t, One) => t
    case (p: PermLiteral, IntLiteral(i)) if i != 0 => FractionPermLiteral(p.literal / Rational(i, 1))
    case (_, _) => new PermIntDiv(t0, t1)
  }

  def unapply(t: PermIntDiv) = Some((t.p0, t.p1))
}

object PermDiv extends ((Term, Term) => Term) {
  import predef.One

  def apply(t0: Term, t1: Term) = PermTimes(t0, FractionPerm(One, t1))
}

class PermPlus(val p0: Term, val p1: Term)
    extends Permissions
       with BinaryOp[Term]
       with StructuralEqualityBinaryOp[Term] {

  override val op = "+"
}

object PermPlus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (NoPerm(), _) => t1
    case (_, NoPerm()) => t0
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal + p1.literal)
    case (FractionPerm(n1, d1), FractionPerm(n2, d2)) if d1 == d2 => FractionPerm(Plus(n1, n2), d1)
    case (PermMinus(t00, t01), _) if t01 == t1 => t00
    case (_, PermMinus(t10, t11)) if t11 == t0 => t10

    case (_, _) => new PermPlus(t0, t1)
  }

  def unapply(pp: PermPlus) = Some((pp.p0, pp.p1))
}

class PermMinus(val p0: Term, val p1: Term)
    extends Permissions
       with BinaryOp[Term]
       with StructuralEqualityBinaryOp[Term] {

  override val op = "-"

  override val toString = p1 match {
    case _: BinaryOp[_] => s"$p0 $op ($p1)"
    case _ => s"$p0 $op $p1"
  }
}

object PermMinus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (_, NoPerm()) => t0
    case (p0, p1) if p0 == p1 => NoPerm()
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal - p1.literal)
    case (p0, PermMinus(p1, p2)) if p0 == p1 => p2
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => new PermMinus(t0, t1)
  }

  def unapply(pm: PermMinus) = Some((pm.p0, pm.p1))
}

class PermLess(val p0: Term, val p1: Term)
    extends BooleanTerm
       with BinaryOp[Term]
       with StructuralEqualityBinaryOp[Term] {

  override val toString = s"($p0) < ($p1)"

  override val op = "<"
}

object PermLess extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = {
    (t0, t1) match {
      case _ if t0 == t1 => False()
      case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal < p1.literal) True() else False()

      case (`t0`, Ite(tCond, tIf, tElse)) =>
        /* The pattern p0 < b ? p1 : p2 arises very often in the context of quantified permissions.
         * Pushing the comparisons into the ite allows further simplifications.
         */
        Ite(tCond, PermLess(t0, tIf), PermLess(t0, tElse))

      case _ => new PermLess(t0, t1)
    }
  }

  def unapply(pl: PermLess) = Some((pl.p0, pl.p1))
}

class PermAtMost(val p0: Term, val p1: Term) extends ComparisonTerm
    with StructuralEqualityBinaryOp[Term] {

  override val op = "<="
}

object PermAtMost extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal <= p1.literal) True() else False()
    case (t0, t1) if t0 == t1 => True()
    case _ => new PermAtMost(e0, e1)
  }

  def unapply(e: PermAtMost) = Some((e.p0, e.p1))
}

class PermMin(val p0: Term, val p1: Term) extends Permissions
    with BinaryOp[Term]
    with StructuralEqualityBinaryOp[Term] {

  utils.assertSort(p0, "Permission 1st", sorts.Perm)
  utils.assertSort(p1, "Permission 2nd", sorts.Perm)

  override val toString = s"min ($p0, $p1)"
}

object PermMin extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term) = (e0, e1) match {
    case (t0, t1) if t0 == t1 => t0
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal > p1.literal) p1 else p0
    case _ => new PermMin(e0, e1)
  }

  def unapply(e: PermMin) = Some((e.p0, e.p1))
}

/* Sequences */

sealed trait SeqTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Seq
}

case class SeqRanged(p0: Term, p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
  utils.assertSort(p0, "first operand", sorts.Int)
  utils.assertSort(p1, "second operand", sorts.Int)

  val elementsSort = sorts.Int
  val sort = sorts.Seq(elementsSort)

  override val toString = s"[$p0..$p1]"
}

case class SeqNil(elementsSort: Sort) extends SeqTerm with Literal {
  val sort = sorts.Seq(elementsSort)
  override val toString = "Nil"
}

case class SeqSingleton(p: Term) extends SeqTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Seq(elementsSort)

  override val toString = s"[$p]"
}

class SeqAppend(val p0: Term, val p1: Term) extends SeqTerm
    with StructuralEqualityBinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val op = "++"
}

object SeqAppend extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Seq](t0, t1)
    new SeqAppend(t0, t1)
  }

  def unapply(sa: SeqAppend) = Some((sa.p0, sa.p1))
}

class SeqDrop(val p0: Term, val p1: Term) extends SeqTerm
    with StructuralEqualityBinaryOp[Term] {

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

class SeqTake(val p0: Term, val p1: Term) extends SeqTerm
    with StructuralEqualityBinaryOp[Term] {

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

class SeqLength(val p: Term) extends Term
    with StructuralEqualityUnaryOp[Term] {

  val sort = sorts.Int
  override val toString = s"|$p|"
}

object SeqLength {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Seq", _.isInstanceOf[sorts.Seq])
    new SeqLength(t)
  }

  def unapply(sl: SeqLength) = Some(sl.p)
}

class SeqAt(val p0: Term, val p1: Term) extends Term
    with StructuralEqualityBinaryOp[Term] {

  val sort = p0.sort.asInstanceOf[sorts.Seq].elementsSort

  override val toString = s"$p0[$p1]"
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
    with StructuralEqualityBinaryOp[Term] {

  override val toString = s"$p1 in $p0"
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
       with StructuralEquality {

  val sort = t0.sort.asInstanceOf[sorts.Seq]
  val elementsSort = sort.elementsSort
  val equalityDefiningMembers = t0 :: t1 :: t2 :: Nil
  override val toString = s"$t0[$t1] := $t2"
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
    with StructuralEqualityBinaryOp[Term] {

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

  override val toString = s"{$p}"
}

class SetAdd(val p0: Term, val p1: Term) extends SetTerm
    with StructuralEqualityBinaryOp[Term] {

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
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetUnion(t0, t1)
  }

  def unapply(su: SetUnion) = Some((su.p0, su.p1))
}

class SetIntersection(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "∩"
}

object SetIntersection extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetIntersection(t0, t1)
  }

  def unapply(si: SetIntersection) = Some((si.p0, si.p1))
}

class SetSubset(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "⊂"
}

object SetSubset extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetSubset(t0, t1)
  }

  def unapply(ss: SetSubset) = Some((ss.p0, ss.p1))
}

class SetDisjoint(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "disj"
}

object SetDisjoint extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetDisjoint(t0, t1)
  }

  def unapply(sd: SetDisjoint) = Some((sd.p0, sd.p1))
}

class SetDifference(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "\\"
}

object SetDifference extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetDifference(t0, t1)
  }

  def unapply(sd: SetDifference) = Some((sd.p0, sd.p1))
}

class SetIn(val p0: Term, val p1: Term) extends BooleanTerm
    with StructuralEqualityBinaryOp[Term] {

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

class SetCardinality(val p: Term) extends Term
    with StructuralEqualityUnaryOp[Term] {

  val sort = sorts.Int
  override val toString = s"|$p|"
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
    with StructuralEqualityBinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

case class EmptyMultiset(elementsSort: Sort) extends MultisetTerm with Literal {
  val sort = sorts.Multiset(elementsSort)
  override val toString = "Ø"
}

case class SingletonMultiset(p: Term) extends MultisetTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Multiset(elementsSort)

  override val toString = s"{$p}"
}

class MultisetAdd(val p0: Term, val p1: Term) extends MultisetTerm
    with StructuralEqualityBinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)

  override val op = "+"
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
}

object MultisetUnion extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetUnion(t0, t1)
  }

  def unapply(mu: MultisetUnion) = Some((mu.p0, mu.p1))
}

class MultisetIntersection(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∩"
}

object MultisetIntersection extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetIntersection(t0, t1)
  }

  def unapply(mi: MultisetIntersection) = Some((mi.p0, mi.p1))
}

class MultisetSubset(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "⊂"
}

object MultisetSubset extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetSubset(t0, t1)
  }

  def unapply(ms: MultisetSubset) = Some((ms.p0, ms.p1))
}

class MultisetDifference(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "\\"
}

object MultisetDifference extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term) = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetDifference(t0, t1)
  }

  def unapply(md: MultisetDifference) = Some((md.p0, md.p1))
}

class MultisetCardinality(val p: Term) extends Term
    with StructuralEqualityUnaryOp[Term] {

  val sort = sorts.Int
  override val toString = s"|$p|"
}

object MultisetCardinality extends (Term => MultisetCardinality) {
  def apply(t: Term) = {
    utils.assertSort(t, "term", "Multiset", _.isInstanceOf[sorts.Multiset])
    new MultisetCardinality(t)
  }

  def unapply(mc: MultisetCardinality) = Some(mc.p)
}

class MultisetCount(val p0: Term, val p1: Term) extends Term
    with StructuralEqualityBinaryOp[Term] {

  val sort = sorts.Int
  override val toString = s"$p0($p1)"
}

object MultisetCount extends {
  def apply(ms: Term, el: Term) = {
    utils.assertSort(ms, "first operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(el, "second operand", ms.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetCount(ms, el)
  }

  def unapply(mc: MultisetCount) = Some((mc.p0, mc.p1))
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

class Combine(val p0: Term, val p1: Term) extends SnapshotTerm
    with StructuralEqualityBinaryOp[Term] {

  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)

  override val toString = s"($p0, $p1)"
}

object Combine extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) = new Combine(t0.convert(sorts.Snap), t1.convert(sorts.Snap))

  def unapply(c: Combine) = Some((c.p0, c.p1))
}

class First(val p: Term) extends SnapshotTerm
    with StructuralEqualityUnaryOp[Term]
    /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object First extends (Term => Term) {
  def apply(t: Term) = t match {
    case Combine(t1, _) => t1
    case _ => new First(t)
  }

  def unapply(f: First) = Some(f.p)
}

class Second(val p: Term) extends SnapshotTerm
    with StructuralEqualityUnaryOp[Term]
    /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object Second extends (Term => Term) {
  def apply(t: Term) = t match {
    case Combine(_, t2) => t2
    case _ => new Second(t)
  }

  def unapply(s: Second) = Some(s.p)
}

/* Quantified permissions */

case class Lookup(field: String, fvf: Term, at: Term) extends Term {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  val sort = fvf.sort.asInstanceOf[sorts.FieldValueFunction].codomainSort
}

case class Domain(field: String, fvf: Term) extends SetTerm /*with PossibleTrigger*/ {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])

  val elementsSort = sorts.Ref
  val sort = sorts.Set(elementsSort)
}


/* Quantified predicates */
case class PredicateLookup(predname: String, psf: Term, args: Seq[Term]) extends Term {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])

  val sort = psf.sort.asInstanceOf[sorts.PredicateSnapFunction].codomainSort
}

case class PredicateDomain(predname: String, psf: Term) extends SetTerm /*with PossibleTrigger*/ {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])
  val elementsSort = sorts.Snap
  val sort = sorts.Set(elementsSort)
}
/* TODO: remove
case class PsfAfterRelation(predname: String, psf2: Term, psf1: Term) extends BooleanTerm {
  utils.assertSameSorts[sorts.PredicateSnapFunction](psf2, psf1)
}

object PsfTop extends (String => Identifier) {
  def apply(predicateName: String): Identifier = Identifier(s"$$psfTOP_$predicateName")
}*/

/* Sort wrappers */

/* Note: Sort wrappers should probably not be used as (outermost) triggers
 * because they are optimised away if wrappee `t` already has sort `to`.
 */

/* Note: Sort wrappers should probably not be used as (outermost) triggers
 * because they are optimised away if wrappee `t` already has sort `to`.
 */
class SortWrapper(val t: Term, val to: Sort)
    extends Term
       with StructuralEquality {

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

/* Magic wands */

case class MagicWandSnapshot(abstractLhs: Term, rhsSnapshot: Term) extends Combine(abstractLhs, rhsSnapshot) {

  utils.assertSort(abstractLhs, "abstract lhs", sorts.Snap)
  utils.assertSort(rhsSnapshot, "rhs", sorts.Snap)

  override val toString = s"wandSnap(lhs = $abstractLhs, rhs = $rhsSnapshot)"

  def merge(other: MagicWandSnapshot, branchConditions: Stack[Term]): MagicWandSnapshot = {
    assert(this.abstractLhs == other.abstractLhs)
    val condition = And(branchConditions)
    MagicWandSnapshot(this.abstractLhs, if (this.rhsSnapshot == other.rhsSnapshot)
      this.rhsSnapshot
    else
      Ite(condition, other.rhsSnapshot, this.rhsSnapshot))
  }
}

object MagicWandSnapshot {
  def apply(snapshot: Term): MagicWandSnapshot = {
    assert(snapshot.sort == sorts.Snap)
    snapshot match {
      case snap: MagicWandSnapshot => snap
      case _ =>
        MagicWandSnapshot(First(snapshot), Second(snapshot))
    }
  }
}

case class MagicWandChunkTerm(chunk: MagicWandChunk) extends Term {
  override val sort = sorts.Unit /* TODO: Does this make sense? */
  override val toString = s"wand@${chunk.id.ghostFreeWand.pos}}"
}

/* Other terms */

class Distinct(val ts: Set[Symbol]) extends BooleanTerm with StructuralEquality {
  assert(ts.nonEmpty, "Distinct requires at least one term")

  val equalityDefiningMembers = ts :: Nil
  override val toString = s"Distinct($ts)"
}

object Distinct extends (Set[Symbol] => Term) {
  def apply(ts: Set[Symbol]): Term =
    if (ts.nonEmpty) new Distinct(ts)
    else True()

  def unapply(d: Distinct) = Some(d.ts)
}

class Let(val bindings: Map[Var, Term], val body: Term) extends Term with StructuralEquality {
  assert(bindings.nonEmpty, "Let needs to bind at least one variable")

  val sort = body.sort
  val equalityDefiningMembers = Seq(body) ++ bindings.flatMap(_.productIterator)

  override lazy val toString = s"let ${bindings.map(p => s"${p._1} = ${p._2}")} in $body"
}

object Let extends ((Map[Var, Term], Term) => Term) {
  def apply(v: Var, t: Term, body: Term): Term = apply(Map(v -> t), body)
  def apply(vs: Seq[Var], ts: Seq[Term], body: Term): Term = apply(toMap(vs zip ts), body)

  def apply(bindings: Map[Var, Term], body: Term) = {
    if (bindings.isEmpty) body
    else new Let(bindings, body)
  }

  def unapply(l: Let) = Some((l.bindings, l.body))
}

/* Predefined terms */

object predef {
  val `?s` = Var(Identifier("s@$"), sorts.Snap) // with SnapshotTerm
  val `?r` = Var(Identifier("r"), sorts.Ref)

  val Zero = IntLiteral(0)
  val One = IntLiteral(1)
}

/* Convenience functions */

object perms {
  def IsNonNegative(p: Term): Term =
    Or(p === NoPerm(), IsPositive(p))
      /* All basic static simplifications should be covered by Equals,
       * IsPositive and or
       */

  def IsPositive(p: Term): Term = p match {
    case p: PermLiteral => if (p.literal > Rational.zero) True() else False()
    case _ => PermLess(NoPerm(), p)
  }

  def IsNonPositive(p: Term): Term = p match {
    case p: PermLiteral => if (p.literal <= Rational.zero) True() else False()
    case _ => Or(p === NoPerm(), PermLess(p, NoPerm()))
  }

  def BigPermSum(it: Iterable[Term], f: Term => Term = t => t): Term =
    viper.silicon.utils.mapReduceLeft(it, f, PermPlus, NoPerm())
}

/* Utility functions */

object utils {
  def consumeExactRead(fp: Term, constrainableARPs: InsertionOrderedSet[Var]): Boolean = fp match {
    case v: Var => !constrainableARPs.contains(v)
    case PermPlus(t0, t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case PermMinus(t0, t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case PermTimes(t0, t1) => consumeExactRead(t0, constrainableARPs) && consumeExactRead(t1, constrainableARPs)
    case IntPermTimes(_, t1) => consumeExactRead(t1, constrainableARPs)
    case PermIntDiv(t0, _) => consumeExactRead(t0, constrainableARPs)
    case PermMin(t0 ,t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case Ite(_, t0, t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case _ => true
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, s: Sort) {
    assert(t.sort == s, s"Expected $desc $t to be of sort $s, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, xs: Seq[Sort]) {
    assert(xs.contains(t.sort), s"Expected $desc $t to be one of sorts $xs, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: String, sortDesc: String, f: Sort => Boolean) {
    assert(f(t.sort), s"Expected $desc $t to be of sort $sortDesc, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSameSorts[S <: Sort with Product : ClassTag](t0: Term, t1: Term) {
    val clazz = implicitly[ClassTag[S]].runtimeClass

    assert(
      (t0.sort, t1.sort) match {
        case (s0: S, s1: S) if s0.productIterator.sameElements(s1.productIterator) => true
        case _ => false
      },
      s"Expected both operands to be of sort ${clazz.getSimpleName}(S1,S2,...), " +
        s"but found $t0 (${t0.sort}) and $t1 (${t1.sort})")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertExpectedSorts(applicable: Applicable, args: Seq[Term]) {
    assert(applicable.argSorts.length == args.length,
           s"Expected ${applicable.argSorts.length} arguments for ${applicable.id}, but got ${args.length}")

    for (i <- args.indices;
         s = applicable.argSorts(i);
         t = args(i)) {

      assert(s == t.sort,
             s"Expected $i-th argument of ${applicable.id} to be of sort $s, but got $t of sort ${t.sort}")
    }
  }

    /* Taken from http://stackoverflow.com/a/8569263.
   * Computes the cartesian product of `xs`.
   */
  def cartesianProduct[A](xs: Traversable[Traversable[A]]): Seq[Seq[A]] =
    xs.foldLeft(Seq(Seq.empty[A])){(x, y) => for (a <- x.view; b <- y) yield a :+ b}
}

object implicits {
  import scala.language.implicitConversions

  implicit def intToTerm(i: Int): IntLiteral = IntLiteral(i)
  implicit def boolToTerm(b: Boolean): BooleanLiteral = if (b) True() else False()
}
