// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state.terms

import scala.annotation.tailrec
import scala.reflect.ClassTag
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Map, Stack, state, toMap}
import viper.silicon.state.{Identifier, MagicWandChunk, MagicWandIdentifier, SortBasedIdentifier}
import viper.silicon.verifier.Verifier
import viper.silicon.annotation.flyweight

sealed trait Node {
  def toString: String
}

sealed trait Symbol extends Node {
  def id: Identifier
}

/*
 * Sorts
 */

sealed trait Sort extends Symbol

object sorts {
  object Snap extends Sort { val id = Identifier("Snap"); override lazy val toString = id.toString }
  object Int  extends Sort { val id = Identifier("Int");  override lazy val toString = id.toString }
  object Bool extends Sort { val id = Identifier("Bool"); override lazy val toString = id.toString }
  object Ref  extends Sort { val id = Identifier("Ref");  override lazy val toString = id.toString }
  object Perm extends Sort { val id = Identifier("Perm"); override lazy val toString = id.toString }
  object Unit extends Sort { val id = Identifier("()");   override lazy val toString = id.toString }

  case class Seq(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Seq[$elementsSort]")
    override lazy val toString = id.toString
  }

  case class Set(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Set[$elementsSort]")
    override lazy val toString = id.toString
  }

  case class Multiset(elementsSort: Sort) extends Sort {
    val id = Identifier(s"Multiset[$elementsSort]")
    override lazy val toString = id.toString
  }

  case class Map(keySort: Sort, valueSort: Sort) extends Sort {
    val id = Identifier(s"Map[$keySort,$valueSort]")
    override lazy val toString = id.toString
  }

  case class UserSort(id: Identifier) extends Sort {
    override lazy val toString = id.toString
  }

  case class SMTSort(id: Identifier) extends Sort {
    override lazy val toString = id.toString
  }

  case class FieldValueFunction(codomainSort: Sort) extends Sort {
    val id = Identifier(s"FVF[$codomainSort]")
    override lazy val toString = id.toString
  }

  case class PredicateSnapFunction(codomainSort: Sort) extends Sort {
    val id = Identifier(s"PSF[$codomainSort]")
    override lazy val toString = id.toString
  }

  case class FieldPermFunction() extends Sort  {
    val id = Identifier("FPM")
    override lazy val toString = id.toString
  }

  case class PredicatePermFunction() extends Sort {
    val id = Identifier("PPM")
    override lazy val toString = id.toString
  }
}

/*
 * Declarations
 */

sealed trait Decl extends Node {
  def id: Identifier
}

@flyweight
class SortDecl(val sort: Sort) extends Decl {
  val id: Identifier = sort.id
}

@flyweight
class FunctionDecl(val func: Function) extends Decl {
  val id: Identifier = func.id
}

@flyweight
class SortWrapperDecl(val from: Sort, val to: Sort) extends Decl {
  val id: Identifier = SortWrapperId(from, to)
}

@flyweight
class MacroDecl(val id: Identifier, val args: Seq[Var], val body: Term) extends Decl

object ConstDecl extends (Var => Decl) { /* TODO: Inconsistent naming - Const vs Var */
  def apply(v: Var) = FunctionDecl(v)
}

object SortWrapperId extends ((Sort, Sort) => Identifier) {
  def apply(from: Sort, to: Sort): Identifier = SortBasedIdentifier("$SortWrappers.%sTo%s", Seq(from, to))
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
  def unapply(fun: Function): Some[(Identifier, Seq[Sort], Sort)] =
    Some((fun.id, fun.argSorts, fun.resultSort))
}

/* RFC: [18-12-2015 Malte] An alternative to using different sub-classes of Function (e.g.
 *      Fun, HeapDepFun, ...) would be to use a single Fun class that as an additional property
 *      (i.e. field) that indicates the kind of
 */

trait GenericFunction[F <: Function] extends Function {
  override lazy val toString =
    if (argSorts.isEmpty) s"$id: $resultSort"
    else s"$id: ${argSorts.mkString(" x ")} -> $resultSort"
}

@flyweight
class Fun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
  extends GenericFunction[Fun]

object Fun extends ((Identifier, Seq[Sort], Sort) => Fun) {
  def apply(id: Identifier, argSort: Sort, resultSort: Sort): Fun =
    apply(id, Seq(argSort), resultSort)
}

/* TODO: [18-12-2015 Malte] Since heap-dependent functions are represented by a separate class,
 *       it might make sense to add methods isLimited/isStateless and transformers
 *       toLimited/toStateless, and to remove the corresponding methods from the FunctionSupporter
 *       object.
 */
@flyweight
class HeapDepFun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
  extends GenericFunction[HeapDepFun]

object HeapDepFun extends ((Identifier, Seq[Sort], Sort) => HeapDepFun) {
  def apply(id: Identifier, argSort: Sort, resultSort: Sort): HeapDepFun =
    apply(id, Seq(argSort), resultSort)
}

@flyweight
class DomainFun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
  extends GenericFunction[DomainFun]

object DomainFun extends ((Identifier, Seq[Sort], Sort) => DomainFun) {
  def apply(id: Identifier, argSort: Sort, resultSort: Sort): DomainFun =
    apply(id, Seq(argSort), resultSort)
}

@flyweight
class SMTFun(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
  extends GenericFunction[SMTFun]

object SMTFun extends ((Identifier, Seq[Sort], Sort) => SMTFun) {
  def apply(id: Identifier, argSort: Sort, resultSort: Sort): SMTFun =
    apply(id, Seq(argSort), resultSort)
}

@flyweight
class Macro(val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort) extends Applicable

@flyweight
class Var(val id: Identifier, val sort: Sort) extends Function with Application[Var] {
  val applicable: Var = this
  val args: Seq[Term] = Seq.empty
  val argSorts: Seq[Sort] = Seq(sorts.Unit)
  val resultSort: Sort = sort

  override lazy val toString = id.toString
}

@flyweight
class App(val applicable: Applicable, val args: Seq[Term])
  extends Application[Applicable] {
  /*with PossibleTrigger*/

  utils.assertExpectedSorts(applicable, args)

  val sort: Sort = applicable.resultSort

  override lazy val toString =
    if (args.isEmpty) applicable.id.toString
    else s"${applicable.id}${args.mkString("(", ", ", ")")}"
}

object App extends ((Applicable, Seq[Term]) => App) {
  def apply(applicable: Applicable, arg: Term): App = App(applicable, Seq(arg))
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

  lazy val subterms: Seq[Term] = state.utils.subterms(this)

  /** @see [[ast.utility.Visitor.visit()]] */
  def visit(f: PartialFunction[Term, Any]): Unit =
    ast.utility.Visitor.visit(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.visitOpt()]] */
  def visitOpt(f: Term => Boolean): Unit =
    ast.utility.Visitor.visitOpt(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.reduceTree()]] */
  def reduceTree[R](f: (Term, Seq[R]) => R): R =
    ast.utility.Visitor.reduceTree(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.existsDefined()]] */
  def existsDefined(f: PartialFunction[Term, Any]): Boolean =
    ast.utility.Visitor.existsDefined(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.hasSubnode()]] */
  def hasSubterm(subterm: Term): Boolean =
    ast.utility.Visitor.hasSubnode(this, subterm, state.utils.subterms)

  /** @see [[ast.utility.Visitor.deepCollect()]] */
  def deepCollect[R](f: PartialFunction[Term, R]) : Seq[R] =
    ast.utility.Visitor.deepCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[Term, R]): Seq[R] =
    ast.utility.Visitor.shallowCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.find()]] */
  def find[R](f: PartialFunction[Term, R]): Option[R] =
    ast.utility.Visitor.find(this, state.utils.subterms)(f)

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

  lazy val freeVariables: InsertionOrderedSet[Var] =
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

  override lazy val toString = s"$op($p)"
}

trait BinaryOp[E] {
  def op: String = getClass.getSimpleName.stripSuffix("$")
  def p0: E
  def p1: E

  override lazy val toString = s"$p0 $op $p1"
}

/* Literals */

sealed trait Literal extends Term

case object Unit extends SnapshotTerm with Literal {
  override lazy val toString = "_"
}

@flyweight
class IntLiteral(val n: BigInt) extends ArithmeticTerm with Literal {
  def +(m: Int) = IntLiteral(n + m)
  def -(m: Int) = IntLiteral(n - m)
  def *(m: Int) = IntLiteral(n * m)
  def /(m: Int) = Div(this, IntLiteral(m))
  override lazy val toString = n.toString()
}

case object Null extends Term with Literal {
  val sort = sorts.Ref
  override lazy val toString = "Null"
}

sealed trait BooleanLiteral extends BooleanTerm with Literal {
  def value: Boolean
  override lazy val toString = value.toString
}

case object True extends BooleanLiteral {
  val value = true
  override lazy val toString = "True"
}

case object False extends BooleanLiteral {
  val value = false
  override lazy val toString = "False"
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

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger], name: String, isGlobal: Boolean) =
    Quantification(Forall, qvar :: Nil, tBody, triggers, name, isGlobal)

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

  def unapply(q: Quantification): Some[(Seq[Var], Term, Seq[Trigger], String, Boolean)] =
    Some(q.vars, q.body, q.triggers, q.name, q.isGlobal)

  override lazy val toString = "QA"
}

object Exists extends Quantifier {
  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvar :: Nil, tBody, triggers)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvars, tBody, triggers)

  def apply(qvars: Iterable[Var], tBody: Term, triggers: Seq[Trigger]) =
    Quantification(Exists, qvars.toSeq, tBody, triggers)

  override lazy val toString = "QE"
}

@flyweight
class Quantification private[terms] (val q: Quantifier, /* TODO: Rename */
                                     val vars: Seq[Var],
                                     val body: Term,
                                     val triggers: Seq[Trigger],
                                     val name: String,
                                     val isGlobal: Boolean)
  extends BooleanTerm {

  def instantiate(terms: Seq[Term]): Term = {
    assert(terms.length == vars.length,
      s"Cannot instantiate a quantifier binding ${vars.length} variables with ${terms.length} terms")

    body.replace(vars, terms)
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

    apply(q, vars, tBody, triggers, name, false)
  }
}

/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

@flyweight
class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
  with BinaryOp[Term] {

  override val op = "+"
}

object Plus extends ((Term, Term) => Term) {
  import predef.Zero

  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (t0, Zero) => t0
    case (Zero, t1) => t1
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 + n1)
    case _ => new Plus(e0, e1)
  }
}

@flyweight
class Minus(val p0: Term, val p1: Term) extends ArithmeticTerm
  with BinaryOp[Term] {

  override val op = "-"
}

object Minus extends ((Term, Term) => Term) {
  import predef.Zero

  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (t0, Zero) => t0
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 - n1)
    case (t0, t1) if t0 == t1 => Zero
    case _ => new Minus(e0, e1)
  }
}

@flyweight
class Times(val p0: Term, val p1: Term) extends ArithmeticTerm
  with BinaryOp[Term] {

  override val op = "*"
}

object Times extends ((Term, Term) => Term) {
  import predef.{Zero, One}

  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (_, Zero) => Zero
    case (Zero, _) => Zero
    case (t0, One) => t0
    case (One, t1) => t1
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 * n1)
    case _ => new Times(e0, e1)
  }
}

@flyweight
class Div(val p0: Term, val p1: Term) extends ArithmeticTerm
  with BinaryOp[Term] {

  override val op = "/"
}

@flyweight
class Mod(val p0: Term, val p1: Term) extends ArithmeticTerm
  with BinaryOp[Term] {

  override val op = "%"
}

/* Boolean expression terms */

sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }

@flyweight
class Not(val p: Term) extends BooleanTerm
  with UnaryOp[Term] {

  override val op = "!"

  override lazy val toString = p match {
    case eq: BuiltinEquals => s"${eq.p0.toString} != ${eq.p1.toString}"
    case _ => s"!($p)"
  }
}

object Not extends (Term => Term) {
  def apply(e0: Term): Term = e0 match {
    case Not(e1) => e1
    case True => False
    case False => True
    case _ => new Not(e0)
  }
}

@flyweight
class Or(val ts: Seq[Term]) extends BooleanTerm {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  override lazy val toString = ts.mkString(" || ")
}

/* TODO: Or should be (Term, Term) => BooleanTerm, but that would require
 *       a Boolean(t: Term) wrapper, because e0/e1 may just be a Var.
 *       It would be sooooo handy to be able to work with Term[Sort], but
 *       that conflicts with using extractor objects to simplify terms,
 *       since extractor objects can't be type-parametrised.
 */
object Or extends (Iterable[Term] => Term) {
  def apply(ts: Term*)(implicit d: DummyImplicit): Term = Or(ts)
  def apply(ts: Iterable[Term]): Term = Or(ts.toSeq)

  //  def apply(e0: Term, e1: Term) = (e0, e1) match {
  //    case (True, _) | (_, True) => True
  //    case (False, _) => e1
  //    case (_, False) => e0
  //    case _ if e0 == e1 => e0
  //    case _ => new Or(e0, e1)
  //  }

  def apply(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case Or(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == False)
    ts = ts.distinct

    ts match {
      case Seq() => False
      case Seq(t) => t
      case _ if ts.contains(True) => True
      case _ => new Or(ts)
    }
  }
}

@flyweight
class And(val ts: Seq[Term]) extends BooleanTerm {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  override lazy val toString = ts.mkString(" && ")
}

object And extends (Iterable[Term] => Term) {
  def apply(ts: Term*)(implicit d: DummyImplicit): Term = And(ts)
  def apply(ts: Iterable[Term]): Term = And(ts.toSeq)

  def apply(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case And(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == True)
    ts = ts.distinct

    ts match {
      case Seq() => True
      case Seq(t) => t
      case _ if ts.contains(False) => False
      case _ => new And(ts)
    }
  }
}

@flyweight
class Implies(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {

  override val op = "==>"
}

object Implies extends ((Term, Term) => Term) {
  @tailrec
  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (True, _) => e1
    case (False, _) => True
    case (_, True) => True
    case (_, Implies(e10, e11)) => Implies(And(e0, e10), e11)
    case _ if e0 == e1 => True
    case _ => new Implies(e0, e1)
  }
}

@flyweight
class Iff(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {

  override val op = "<==>"
}

object Iff extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (True, _) => e1
    case (_, True) => e0
    case _ if e0 == e1 => True
    case _ => new Iff(e0, e1)
  }
}

@flyweight
class Ite(val t0: Term, val t1: Term, val t2: Term)
  extends Term {

  assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
    s"Ite term Ite($t0, $t1, $t2) is not well-sorted: ${t0.sort}, ${t1.sort}, ${t2.sort}")

  val sort = t1.sort
  override lazy val toString = s"($t0 ? $t1 : $t2)"
}

object Ite extends ((Term, Term, Term) => Term) {
  def apply(e0: Term, e1: Term, e2: Term): Term = (e0, e1, e2) match {
    case _ if e1 == e2 => e1
    case (True, _, _) => e1
    case (False, _, _) => e2
    case (_, True, False) => e0
    case (_, False, True) => Not(e0)
    case _ => new Ite(e0, e1, e2)
  }
}

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

sealed trait Equals extends ComparisonTerm with BinaryOp[Term] { override val op = "==" }

object Equals extends ((Term, Term) => BooleanTerm) {
  def apply(e0: Term, e1: Term) = {
    assert(e0.sort == e1.sort,
      s"Expected both operands to be of the same sort, but found ${e0.sort} ($e0) and ${e1.sort} ($e1).")

    if (e0 == e1)
      True
    else
      e0.sort match {
        case sorts.Snap =>
          (e0, e1) match {
            case (sw1: SortWrapper, sw2: SortWrapper) if sw1.t.sort != sw2.t.sort =>
              assert(false, s"Equality '(Snap) $e0 == (Snap) $e1' is not allowed")
            /* The next few cases are nonsensical and might indicate a bug in Silicon.
               However, they can also arise on infeasible paths (and preventing them
               would require potentially expensive prover calls), so treating
               them as errors is unfortunately not an option.
             */
            // case (_: Combine, _: SortWrapper) =>
            //   assert(false, s"Equality '$e0 == (Snap) $e1' is not allowed")
            // case (_: SortWrapper, _: Combine) =>
            //   assert(false, s"Equality '(Snap) $e0 == $e1' is not allowed")
            // case (Unit, _: Combine) | (_: Combine, Unit) =>
            //   assert(false, s"Equality '$e0 == $e1' is not allowed")
            case _ => /* Ok */
          }

          BuiltinEquals(e0, e1)

        case _: sorts.Seq | _: sorts.Set | _: sorts.Multiset | _: sorts.Map => CustomEquals(e0, e1)
        case _ => BuiltinEquals(e0, e1)
      }
  }

  def unapply(e: Equals) = Some((e.p0, e.p1))
}

/* Represents built-in equality, e.g., '=' in SMT-LIB */
@flyweight
class BuiltinEquals private[terms] (val p0: Term, val p1: Term) extends Equals
  with BinaryOp[Term]

object BuiltinEquals extends ((Term, Term) => BooleanTerm) {
  def apply(t1: Term, t2: Term): BooleanTerm = (t1, t2) match {
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal == p1.literal) True else False
    case _ => new BuiltinEquals(t1, t2)
  }
}

/* Custom equality that (potentially) needs to be axiomatised. */
@flyweight
class CustomEquals private[terms] (val p0: Term, val p1: Term) extends Equals
  with BinaryOp[Term] {

  override val op = "==="
}

@flyweight
class Less(val p0: Term, val p1: Term) extends ComparisonTerm
  with BinaryOp[Term] {

  assert(p0.sort == p1.sort,
    s"Expected both operands to be of the same sort, but found ${p0.sort} ($p0) and ${p1.sort} ($p1).")

  override val op = "<"
}

object Less extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): BooleanTerm = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True else False
    case (t0, t1) if t0 == t1 => False
    case _ => new Less(e0, e1)
  }
}

@flyweight
class AtMost(val p0: Term, val p1: Term) extends ComparisonTerm
  with BinaryOp[Term] {

  override val op = "<="
}

object AtMost extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): BooleanTerm = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => new AtMost(e0, e1)
  }
}

@flyweight
class Greater(val p0: Term, val p1: Term) extends ComparisonTerm
  with BinaryOp[Term] {

  override val op = ">"
}

object Greater extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): BooleanTerm = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True else False
    case (t0, t1) if t0 == t1 => False
    case _ => new Greater(e0, e1)
  }
}

@flyweight
class AtLeast(val p0: Term, val p1: Term) extends ComparisonTerm
  with BinaryOp[Term] {

  override val op = ">="
}

object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): BooleanTerm = (e0, e1) match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => new AtLeast(e0, e1)
  }
}

/*
 * Permissions
 */

sealed trait Permissions extends Term {
  val sort = sorts.Perm
}

sealed abstract class PermLiteral(val literal: Rational) extends Permissions

@flyweight
class NoPerm() extends PermLiteral(Rational.zero) { override lazy val toString = "Z" }
@flyweight
class FullPerm() extends PermLiteral(Rational.one) { override lazy val toString = "W" }

@flyweight
class FractionPermLiteral(val r: Rational) extends PermLiteral(r) {
  override lazy val toString = literal.toString
}

object FractionPermLiteral extends (Rational => Permissions) {
  def apply(r: Rational): PermLiteral = r match {
    case Rational(n, _) if n == 0 => NoPerm()
    case Rational(n, d) if n == d => FullPerm()
    case _ => new FractionPermLiteral(r)
  }
}

@flyweight
class FractionPerm(val n: Term, val d: Term)
  extends Permissions {

  override lazy val toString = s"$n/$d"
}

object FractionPerm extends ((Term, Term) => Permissions) {
  def apply(n: Term, d: Term): Permissions = (n, d) match {
    case (IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => FractionPermLiteral(Rational(i1, i2))
    case _ => new FractionPerm(n, d)
  }
}

@flyweight
class IsValidPermVal(val t: Term) extends BooleanTerm {
  override lazy val toString = s"PVar($v)"
}

@flyweight
class IsReadPermVar(val v: Var, val ub: Term) extends BooleanTerm {
  override lazy val toString = s"RdVar($v, $ub)"
}

@flyweight
class PermTimes(val p0: Term, val p1: Term)
  extends Permissions
    with BinaryOp[Term] {

  override val op = "*"
}

object PermTimes extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = (t0, t1) match {
    case (FullPerm(), t) => t
    case (t, FullPerm()) => t
    case (NoPerm(), _) => NoPerm()
    case (_, NoPerm()) => NoPerm()
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal * p1.literal)
    case (_, _) => new PermTimes(t0, t1)
  }
}

@flyweight
class IntPermTimes(val p0: Term, val p1: Term)
  extends Permissions
    with BinaryOp[Term] {

  override val op = "*"
}

object IntPermTimes extends ((Term, Term) => Term) {
  import predef.{Zero, One}

  def apply(t0: Term, t1: Term): Term = (t0, t1) match {
    case (Zero, _) => NoPerm()
    case (One, t) => t
    case (_, NoPerm()) => NoPerm()
    case (IntLiteral(i), p: PermLiteral) => FractionPermLiteral(Rational(i, 1) * p.literal)
    case (_, _) => new IntPermTimes(t0, t1)
  }
}

@flyweight
class PermIntDiv(val p0: Term, val p1: Term)
  extends Permissions
    with BinaryOp[Term] {

  utils.assertSort(p1, "Second term", sorts.Int)

  override val op = "/"
}

object PermIntDiv extends ((Term, Term) => Term) {
  import predef.One

  def apply(t0: Term, t1: Term): Term = (t0, t1) match {
    case (t, One) => t
    case (p: PermLiteral, IntLiteral(i)) if i != 0 => FractionPermLiteral(p.literal / Rational(i, 1))
    case (_, _) => new PermIntDiv(t0, t1)
  }
}

object PermDiv extends ((Term, Term) => Term) {
  import predef.One

  def apply(t0: Term, t1: Term) = PermTimes(t0, FractionPerm(One, t1))
}

@flyweight
class PermPlus(val p0: Term, val p1: Term)
  extends Permissions
    with BinaryOp[Term] {

  override val op = "+"
}

object PermPlus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = (t0, t1) match {
    case (NoPerm(), _) => t1
    case (_, NoPerm()) => t0
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal + p1.literal)
    case (FractionPerm(n1, d1), FractionPerm(n2, d2)) if d1 == d2 => FractionPerm(Plus(n1, n2), d1)
    case (PermMinus(t00, t01), _) if t01 == t1 => t00
    case (_, PermMinus(t10, t11)) if t11 == t0 => t10

    case (_, _) => new PermPlus(t0, t1)
  }
}

@flyweight
class PermMinus(val p0: Term, val p1: Term)
  extends Permissions
    with BinaryOp[Term] {

  override val op = "-"

  override lazy val toString = p1 match {
    case _: BinaryOp[_] => s"$p0 $op ($p1)"
    case _ => s"$p0 $op $p1"
  }
}

object PermMinus extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = (t0, t1) match {
    case (_, NoPerm()) => t0
    case (p0, p1) if p0 == p1 => NoPerm()
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal - p1.literal)
    case (p0, PermMinus(p1, p2)) if p0 == p1 => p2
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => new PermMinus(t0, t1)
  }
}

@flyweight
class PermLess(val p0: Term, val p1: Term)
  extends BooleanTerm
    with BinaryOp[Term] {

  override lazy val toString = s"($p0) < ($p1)"

  override val op = "<"
}

object PermLess extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Term = {
    (t0, t1) match {
      case _ if t0 == t1 => False
      case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal < p1.literal) True else False

      case (`t0`, Ite(tCond, tIf, tElse)) =>
        /* The pattern p0 < b ? p1 : p2 arises very often in the context of quantified permissions.
         * Pushing the comparisons into the ite allows further simplifications.
         */
        Ite(tCond, PermLess(t0, tIf), PermLess(t0, tElse))

      case _ => new PermLess(t0, t1)
    }
  }
}

@flyweight
class PermAtMost(val p0: Term, val p1: Term) extends ComparisonTerm
  with BinaryOp[Term] {

  override val op = "<="
}

object PermAtMost extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): BooleanTerm = (e0, e1) match {
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal <= p1.literal) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => new PermAtMost(e0, e1)
  }
}

@flyweight
class PermMin(val p0: Term, val p1: Term) extends Permissions
  with BinaryOp[Term] {

  utils.assertSort(p0, "Permission 1st", sorts.Perm)
  utils.assertSort(p1, "Permission 2nd", sorts.Perm)

  override lazy val toString = s"min ($p0, $p1)"
}

object PermMin extends ((Term, Term) => Term) {
  def apply(e0: Term, e1: Term): Term = (e0, e1) match {
    case (t0, t1) if t0 == t1 => t0
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal > p1.literal) p1 else p0
    case _ => new PermMin(e0, e1)
  }
}

/* Sequences */

sealed trait SeqTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Seq
}

@flyweight
class SeqRanged(val p0: Term, val p1: Term) extends SeqTerm /* with BinaryOp[Term] */ {
  utils.assertSort(p0, "first operand", sorts.Int)
  utils.assertSort(p1, "second operand", sorts.Int)

  val elementsSort = sorts.Int
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = s"[$p0..$p1]"
}

@flyweight
class SeqNil(val elementsSort: Sort) extends SeqTerm with Literal {
  val sort = sorts.Seq(elementsSort)
  override lazy val toString = "Nil"
}

@flyweight
class SeqSingleton(val p: Term) extends SeqTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = s"[$p]"
}

@flyweight
class SeqAppend(val p0: Term, val p1: Term) extends SeqTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val op = "++"
}

object SeqAppend extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term): SeqAppend = {
    utils.assertSameSorts[sorts.Seq](t0, t1)
    new SeqAppend(t0, t1)
  }
}

@flyweight
class SeqDrop(val p0: Term, val p1: Term) extends SeqTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = p0.toString + "[" + p1.toString + ":]"
}

object SeqDrop extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term): SeqDrop = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqDrop(t0, t1)
  }
}

@flyweight
class SeqTake(val p0: Term, val p1: Term) extends SeqTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = p0.toString + "[:" + p1.toString + "]"
}

object SeqTake extends ((Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term): SeqTake = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqTake(t0, t1)
  }
}

@flyweight
class SeqLength(val p: Term) extends Term
  with UnaryOp[Term] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object SeqLength {
  def apply(t: Term): SeqLength = {
    utils.assertSort(t, "term", "Seq", _.isInstanceOf[sorts.Seq])
    new SeqLength(t)
  }
}

@flyweight
class SeqAt(val p0: Term, val p1: Term) extends Term
  with BinaryOp[Term] {

  val sort = p0.sort.asInstanceOf[sorts.Seq].elementsSort

  override lazy val toString = s"$p0[$p1]"
}

object SeqAt extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): SeqAt = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    new SeqAt(t0, t1)
  }
}

@flyweight
class SeqIn(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {

  override lazy val toString = s"$p1 in $p0"
}

object SeqIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): SeqIn = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    new SeqIn(t0, t1)
  }
}

@flyweight
class SeqInTrigger(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {

  override lazy val toString = s"$p1 in $p0"
}

object SeqInTrigger extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): SeqInTrigger = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    new SeqInTrigger(t0, t1)
  }
}

@flyweight
class SeqUpdate(val t0: Term, val t1: Term, val t2: Term)
  extends SeqTerm {

  val sort = t0.sort.asInstanceOf[sorts.Seq]
  val elementsSort = sort.elementsSort
  override lazy val toString = s"$t0[$t1] := $t2"
}

object SeqUpdate extends ((Term, Term, Term) => SeqTerm) {
  def apply(t0: Term, t1: Term, t2: Term): SeqUpdate = {
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    utils.assertSort(t2, "third operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)

    new SeqUpdate(t0, t1, t2)
  }
}

/* Sets */

sealed trait SetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Set
}

sealed trait BinarySetOp extends SetTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)
}

@flyweight
class EmptySet(val elementsSort: Sort) extends SetTerm with Literal {
  val sort = sorts.Set(elementsSort)
  override lazy val toString = "Ø"
}

@flyweight
class SingletonSet(val p: Term) extends SetTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Set(elementsSort)

  override lazy val toString = s"{$p}"
}

@flyweight
class SetAdd(val p0: Term, val p1: Term) extends SetTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)

  override val op = "+"
}

object SetAdd extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term): SetAdd = {
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Set].elementsSort)

    new SetAdd(t0, t1)
  }
}

@flyweight
class SetUnion(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "∪"
}

object SetUnion extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term): SetUnion = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetUnion(t0, t1)
  }
}

@flyweight
class SetIntersection(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "∩"
}

object SetIntersection extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term): SetIntersection = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetIntersection(t0, t1)
  }
}

@flyweight
class SetSubset(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {
  override val op = "⊂"
}

object SetSubset extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): SetSubset = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetSubset(t0, t1)
  }
}

@flyweight
class SetDisjoint(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {
  override val op = "disj"
}

object SetDisjoint extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): SetDisjoint = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetDisjoint(t0, t1)
  }
}

@flyweight
class SetDifference(val p0: Term, val p1: Term) extends BinarySetOp {
  override val op = "\\"
}

object SetDifference extends ((Term, Term) => SetTerm) {
  def apply(t0: Term, t1: Term): SetDifference = {
    utils.assertSameSorts[sorts.Set](t0, t1)
    new SetDifference(t0, t1)
  }
}

@flyweight
class SetIn(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {

  override val op = "in"
}

object SetIn extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): SetIn = {
    utils.assertSort(t1, "second operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Set].elementsSort)

    new SetIn(t0, t1)
  }
}

@flyweight
class SetCardinality(val p: Term) extends Term
  with UnaryOp[Term] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object SetCardinality extends (Term => SetCardinality) {
  def apply(t: Term): SetCardinality = {
    utils.assertSort(t, "term", "Set", _.isInstanceOf[sorts.Set])
    new SetCardinality(t)
  }
}

/* Multisets */

sealed trait MultisetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Multiset
}

sealed trait BinaryMultisetOp extends MultisetTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

@flyweight
class EmptyMultiset(val elementsSort: Sort) extends MultisetTerm with Literal {
  val sort = sorts.Multiset(elementsSort)
  override lazy val toString = "Ø"
}

@flyweight
class SingletonMultiset(val p: Term) extends MultisetTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Multiset(elementsSort)

  override lazy val toString = s"{$p}"
}

@flyweight
class MultisetAdd(val p0: Term, val p1: Term) extends MultisetTerm
  with BinaryOp[Term] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)

  override val op = "+"
}

object MultisetAdd extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term): MultisetAdd = {
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetAdd(t0, t1)
  }
}

@flyweight
class MultisetUnion(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∪"
}

object MultisetUnion extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term): MultisetUnion = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetUnion(t0, t1)
  }
}

@flyweight
class MultisetIntersection(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "∩"
}

object MultisetIntersection extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term): MultisetIntersection = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetIntersection(t0, t1)
  }
}

@flyweight
class MultisetSubset(val p0: Term, val p1: Term) extends BooleanTerm
  with BinaryOp[Term] {
  override val op = "⊂"
}

object MultisetSubset extends ((Term, Term) => BooleanTerm) {
  def apply(t0: Term, t1: Term): MultisetSubset = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetSubset(t0, t1)
  }
}

@flyweight
class MultisetDifference(val p0: Term, val p1: Term) extends BinaryMultisetOp {
  override val op = "\\"
}

object MultisetDifference extends ((Term, Term) => MultisetTerm) {
  def apply(t0: Term, t1: Term): MultisetDifference = {
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    new MultisetDifference(t0, t1)
  }
}

@flyweight
class MultisetCardinality(val p: Term) extends Term
  with UnaryOp[Term] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object MultisetCardinality extends (Term => MultisetCardinality) {
  def apply(t: Term): MultisetCardinality = {
    utils.assertSort(t, "term", "Multiset", _.isInstanceOf[sorts.Multiset])
    new MultisetCardinality(t)
  }
}

@flyweight
class MultisetCount(val p0: Term, val p1: Term) extends Term
  with BinaryOp[Term] {

  val sort = sorts.Int
  override lazy val toString = s"$p0($p1)"
}

object MultisetCount extends {
  def apply(ms: Term, el: Term): MultisetCount = {
    utils.assertSort(ms, "first operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(el, "second operand", ms.sort.asInstanceOf[sorts.Multiset].elementsSort)

    new MultisetCount(ms, el)
  }
}

/* Maps */

sealed trait MapTerm extends Term {
  val keySort: Sort
  val valueSort: Sort
  val sort: sorts.Map
}

@flyweight
class EmptyMap(val keySort: Sort, val valueSort: Sort) extends MapTerm with Literal {
  val sort = sorts.Map(keySort, valueSort)
  override lazy val toString = "Ø"
}

@flyweight
class MapLookup(val base: Term, val key: Term) extends Term with BinaryOp[Term] {
  val sort: Sort = p0.sort.asInstanceOf[sorts.Map].valueSort
  override def p0: Term = base
  override def p1: Term = key
  override lazy val toString = s"$p0[$p1]"
}

object MapLookup extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term) : Term = {
    utils.assertSort(t0, "first operand", "Map", _.isInstanceOf[sorts.Map])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Map].keySort)
    new MapLookup(t0, t1)
  }
}

@flyweight
class MapCardinality(val p: Term) extends Term with UnaryOp[Term] {
  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object MapCardinality extends (Term => MapCardinality) {
  def apply(t: Term) : MapCardinality = {
    utils.assertSort(t, "term", "Map", _.isInstanceOf[sorts.Map])
    new MapCardinality(t)
  }
}

@flyweight
class MapUpdate(val base: Term, val key: Term, val value: Term) extends MapTerm {
  override val sort: sorts.Map = base.sort.asInstanceOf[sorts.Map]
  override val keySort: Sort = sort.keySort
  override val valueSort: Sort = sort.valueSort
}

object MapUpdate extends ((Term, Term, Term) => MapTerm) {
  def apply(t0: Term, t1: Term, t2: Term) : MapUpdate = {
    utils.assertSort(t0, "first operand", "Map", _.isInstanceOf[sorts.Map])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Map].keySort)
    utils.assertSort(t2, "third operand", t0.sort.asInstanceOf[sorts.Map].valueSort)
    new MapUpdate(t0, t1, t2)
  }
}

@flyweight
class MapDomain(val p: Term) extends SetTerm with UnaryOp[Term] {
  override val elementsSort: Sort = p.sort.asInstanceOf[sorts.Map].keySort
  override val sort: sorts.Set = sorts.Set(elementsSort)
  override lazy val toString = s"domain($p)"
}

object MapDomain extends (Term => SetTerm) {
  def apply(t0: Term) : SetTerm = {
    utils.assertSort(t0, "term", "Map", _.isInstanceOf[sorts.Map])
    new MapDomain(t0)
  }
}

@flyweight
class MapRange(val p: Term) extends SetTerm with UnaryOp[Term] {
  override val elementsSort: Sort = p.sort.asInstanceOf[sorts.Map].valueSort
  override val sort: sorts.Set = sorts.Set(elementsSort)
  override lazy val toString = s"range($p)"
}

object MapRange extends (Term => SetTerm) {
  def apply(t0: Term) : SetTerm = {
    utils.assertSort(t0, "term", "Map", _.isInstanceOf[sorts.Map])
    new MapRange(t0)
  }
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

@flyweight
class Combine(val p0: Term, val p1: Term) extends SnapshotTerm
  with BinaryOp[Term] {

  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)

  override lazy val toString = s"($p0, $p1)"
}

object Combine extends ((Term, Term) => Term) {
  def apply(t0: Term, t1: Term): Combine = new Combine(t0.convert(sorts.Snap), t1.convert(sorts.Snap))
}

@flyweight
class First(val p: Term) extends SnapshotTerm
  with UnaryOp[Term]
  /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object First extends (Term => Term) {
  def apply(t: Term): Term = t match {
    case Combine(t1, _) => t1
    case _ => new First(t)
  }
}

@flyweight
class Second(val p: Term) extends SnapshotTerm
  with UnaryOp[Term]
  /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object Second extends (Term => Term) {
  def apply(t: Term): Term = t match {
    case Combine(_, t2) => t2
    case _ => new Second(t)
  }
}

/* Quantified permissions */

@flyweight
class Lookup(val field: String, val fvf: Term, val at: Term) extends Term {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  val sort = fvf.sort.asInstanceOf[sorts.FieldValueFunction].codomainSort
}

@flyweight
class PermLookup(val field: String, val pm: Term, val at: Term) extends Term {
  utils.assertSort(pm, "field perm function", "FieldPermFunction", _.isInstanceOf[sorts.FieldPermFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  val sort = sorts.Perm
}

@flyweight
class Domain(val field: String, val fvf: Term) extends SetTerm /*with PossibleTrigger*/ {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])

  val elementsSort = sorts.Ref
  val sort = sorts.Set(elementsSort)
}

@flyweight
class FieldTrigger(val field: String, val fvf: Term, val at: Term) extends Term {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  val sort = sorts.Bool
}

/* Quantified predicates */

@flyweight
class PredicateLookup(val predname: String, val psf: Term, val args: Seq[Term]) extends Term {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])

  val sort = psf.sort.asInstanceOf[sorts.PredicateSnapFunction].codomainSort
}

@flyweight
class PredicatePermLookup(val predname: String, val pm: Term, val args: Seq[Term]) extends Term {
  utils.assertSort(pm, "predicate perm function", "PredicatePermFunction", _.isInstanceOf[sorts.PredicatePermFunction])

  val sort = sorts.Perm
}

@flyweight
class PredicateDomain(val predname: String, val psf: Term) extends SetTerm /*with PossibleTrigger*/ {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])
  val elementsSort = sorts.Snap
  val sort = sorts.Set(elementsSort)
}

@flyweight
class PredicateTrigger(val predname: String, val psf: Term, val args: Seq[Term]) extends Term {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])

  val sort = sorts.Bool
}

/* Magic wands */
@flyweight(false)
class MagicWandSnapshot(val abstractLhs: Term, val rhsSnapshot: Term) extends Combine(abstractLhs, rhsSnapshot) {
  utils.assertSort(abstractLhs, "abstract lhs", sorts.Snap)
  utils.assertSort(rhsSnapshot, "rhs", sorts.Snap)

  override lazy val toString = s"wandSnap(lhs = $abstractLhs, rhs = $rhsSnapshot)"

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

@flyweight
class MagicWandChunkTerm(val chunk: MagicWandChunk) extends Term {
  override val sort = sorts.Unit /* TODO: Does this make sense? */
  override lazy val toString = s"wand@${chunk.id.ghostFreeWand.pos}}"
}

/* Factory methods for all resources */

object toSnapTree extends (Seq[Term] => Term) {
  @inline
  def apply(args: Seq[Term]): Term = {
    if (args.isEmpty) Unit
    else args.map(_.convert(sorts.Snap)).reduceLeft(Combine)
  }
}

object fromSnapTree extends ((Term, Int) => Seq[Term]) {
  def apply(snap: Term, targets: Seq[Term]): Seq[Term] = {
    fromSnapTree(snap, targets.length)
      .zip(targets)
      .map { case (s, t) => s.convert(t.sort) }
  }

  def apply(snap: Term, size: Int): Seq[Term] = {
    if (size <= 1) Seq(snap)
    else fromSnapTree(First(snap), size - 1) :+ Second(snap)
  }
}

object ResourceTriggerFunction {
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term]): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): FieldTrigger =
    FieldTrigger(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicateTrigger =
    PredicateTrigger(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term]): PredicateTrigger = {
    val wandId = MagicWandIdentifier(wand, Verifier.program).toString

    PredicateTrigger(wandId, sm, args)
  }
}

object ResourceLookup {
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term]): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): Lookup =
    Lookup(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicateLookup =
    PredicateLookup(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term]): PredicateLookup = {
    val wandId = MagicWandIdentifier(wand, Verifier.program).toString

    PredicateLookup(wandId, sm, args)
  }
}

object ResourcePermissionLookup {
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term]): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): PermLookup =
    PermLookup(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicatePermLookup =
    PredicatePermLookup(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term]): PredicatePermLookup = {
    val wandId = MagicWandIdentifier(wand, Verifier.program).toString

    PredicatePermLookup(wandId, sm, args)
  }
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
@flyweight
class SortWrapper(val t: Term, val to: Sort)
  extends Term {

  assert((t.sort == sorts.Snap || to == sorts.Snap) && t.sort != to,
    s"Unexpected sort wrapping of $t from ${t.sort} to $to")

  //  override lazy val toString = s"SortWrapper($t, $to)"
  override lazy val toString = t.toString
  override val sort = to
}

object SortWrapper {
  def apply(t: Term, to: Sort): Term = t match {
    case _ if t.sort == to => t
    case sw: SortWrapper if sw.t.sort == to => sw.t
    case _ => new SortWrapper(t, to)
  }
}

/* Other terms */

@flyweight
class Distinct(val ts: Set[Symbol]) extends BooleanTerm {
  assert(ts.nonEmpty, "Distinct requires at least one term")

  override lazy val toString = s"Distinct($ts)"
}

object Distinct extends (Set[Symbol] => Term) {
  def apply(ts: Set[Symbol]): Term =
    if (ts.nonEmpty) new Distinct(ts)
    else True
}

@flyweight
class Let(val bindings: Map[Var, Term], val body: Term) extends Term {
  assert(bindings.nonEmpty, "Let needs to bind at least one variable")

  val sort = body.sort

  override lazy val toString = s"let ${bindings.map(p => s"${p._1} = ${p._2}")} in $body"
}

object Let extends ((Map[Var, Term], Term) => Term) {
  def apply(v: Var, t: Term, body: Term): Term = apply(Map(v -> t), body)
  def apply(vs: Seq[Var], ts: Seq[Term], body: Term): Term = apply(toMap(vs zip ts), body)

  def apply(bindings: Map[Var, Term], body: Term): Term = {
    if (bindings.isEmpty) body
    else new Let(bindings, body)
  }
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
    case p: PermLiteral => if (p.literal > Rational.zero) True else False
    case _ => PermLess(NoPerm(), p)
  }

  def IsNonPositive(p: Term): Term = p match {
    case p: PermLiteral => if (p.literal <= Rational.zero) True else False
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
    case PermPermDiv(t0, t1) => consumeExactRead(t0, constrainableARPs) && consumeExactRead(t1, constrainableARPs)
    case PermMin(t0 ,t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case Ite(_, t0, t1) => consumeExactRead(t0, constrainableARPs) || consumeExactRead(t1, constrainableARPs)
    case _ => true
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: => String, s: Sort): Unit = {
    assert(t.sort == s, s"Expected $desc $t to be of sort $s, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: => String, xs: Seq[Sort]): Unit = {
    assert(xs.contains(t.sort), s"Expected $desc $t to be one of sorts $xs, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSort(t: Term, desc: => String, sortDesc: String, f: Sort => Boolean): Unit = {
    assert(f(t.sort), s"Expected $desc $t to be of sort $sortDesc, but found ${t.sort}.")
  }

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  def assertSameSorts[S <: Sort with Product : ClassTag](t0: Term, t1: Term): Unit = {
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
  def assertExpectedSorts(applicable: Applicable, args: Seq[Term]): Unit = {
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
  def cartesianProduct[A](xs: Iterable[Iterable[A]]): Seq[Seq[A]] =
    xs.foldLeft(Seq(Seq.empty[A])){(x, y) => for (a <- x; b <- y) yield a :+ b}
}

object implicits {
  import scala.language.implicitConversions

  implicit def intToTerm(i: Int): IntLiteral = IntLiteral(i)
  implicit def boolToTerm(b: Boolean): BooleanLiteral = if (b) True else False
}
