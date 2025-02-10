// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state.terms

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.reflect.ClassTag
import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Map, Stack, state, toMap}
import viper.silicon.state.{Identifier, MagicWandChunk, MagicWandIdentifier, SortBasedIdentifier}
import viper.silicon.verifier.Verifier
import viper.silver.utility.Common.Rational

import scala.collection.concurrent.TrieMap

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

  case class FieldValueFunction(codomainSort: Sort, fieldName: String) extends Sort {
    val id = Identifier(s"FVF[$fieldName]")
    override lazy val toString = id.toString
  }

  case class PredicateSnapFunction(codomainSort: Sort, predName: String) extends Sort {
    val id = Identifier(s"PSF[$predName]")
    override lazy val toString = id.toString
  }

  object MagicWandSnapFunction extends Sort {
    val id: Identifier = Identifier("MWSF")
    override lazy val toString: String = id.toString
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

class SortDecl private[terms] (val sort: Sort) extends Decl with ConditionalFlyweight[Sort, SortDecl] {
  val id: Identifier = sort.id
  override val equalityDefiningMembers: Sort = sort
}

object SortDecl extends CondFlyweightFactory[Sort, SortDecl, SortDecl] {
  override def actualCreate(args: Sort): SortDecl = new SortDecl(args)
}

class FunctionDecl private[terms] (val func: Function) extends Decl with ConditionalFlyweight[Function, FunctionDecl] {
  val id: Identifier = func.id
  override val equalityDefiningMembers: Function = func
}

object FunctionDecl extends CondFlyweightFactory[Function, FunctionDecl, FunctionDecl] {
  override def actualCreate(args: Function): FunctionDecl = new FunctionDecl(args)
}

class SortWrapperDecl private[terms] (val from: Sort, val to: Sort) extends Decl with ConditionalFlyweight[(Sort, Sort), SortWrapperDecl] {
  val id: Identifier = SortWrapperId(from, to)
  override val equalityDefiningMembers: (Sort, Sort) = (from, to)
}

object SortWrapperDecl extends CondFlyweightFactory[(Sort, Sort), SortWrapperDecl, SortWrapperDecl] {
  override def actualCreate(args: (Sort, Sort)): SortWrapperDecl = new SortWrapperDecl(args._1, args._2)
}

class MacroDecl private[terms] (val id: Identifier, val args: Seq[Var], val body: Term) extends Decl with ConditionalFlyweight[(Identifier, Seq[Var], Term), MacroDecl] {
  override val equalityDefiningMembers: (Identifier, Seq[Var], Term) = (id, args, body)
}

object MacroDecl extends CondFlyweightFactory[(Identifier, Seq[Var], Term), MacroDecl, MacroDecl] {
  override def actualCreate(args: (Identifier, Seq[Var], Term)): MacroDecl = new MacroDecl(args._1, args._2, args._3)
}

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
  val equalityDefiningMembers = (id, argSorts, resultSort)

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort): F

  override lazy val toString =
    if (argSorts.isEmpty) s"$id: $resultSort"
    else s"$id: ${argSorts.mkString(" x ")} -> $resultSort"
}

trait GenericFunctionCompanion[F <: Function] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort): F

  def apply(id: Identifier, argSort: Sort, resultSort: Sort): F =
    apply(id, Seq(argSort), resultSort)
}

class Fun private[terms] (val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends ConditionalFlyweight[(Identifier, Seq[Sort], Sort), Fun] with GenericFunction[Fun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    Fun(id, argSorts, resultSort)
}

object Fun extends CondFlyweightFactory[(Identifier, Seq[Sort], Sort), Fun, Fun] with GenericFunctionCompanion[Fun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = createIfNonExistent((id, argSorts, resultSort))

  override def actualCreate(args: (Identifier, Seq[Sort], Sort)): Fun = new Fun(args._1, args._2, args._3)
}

/* TODO: [18-12-2015 Malte] Since heap-dependent functions are represented by a separate class,
 *       it might make sense to add methods isLimited/isStateless and transformers
 *       toLimited/toStateless, and to remove the corresponding methods from the FunctionSupporter
 *       object.
 */
class HeapDepFun private[terms] (val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends ConditionalFlyweight[(Identifier, Seq[Sort], Sort), HeapDepFun] with GenericFunction[HeapDepFun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    HeapDepFun(id, argSorts, resultSort)
}

object HeapDepFun extends CondFlyweightFactory[(Identifier, Seq[Sort], Sort), HeapDepFun, HeapDepFun] with GenericFunctionCompanion[HeapDepFun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = createIfNonExistent((id, argSorts, resultSort))

  override def actualCreate(args: (Identifier, Seq[Sort], Sort)): HeapDepFun = new HeapDepFun(args._1, args._2, args._3)
}

class DomainFun private[terms] (val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
    extends ConditionalFlyweight[(Identifier, Seq[Sort], Sort), DomainFun] with GenericFunction[DomainFun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
    DomainFun(id, argSorts, resultSort)
}

object DomainFun extends CondFlyweightFactory[(Identifier, Seq[Sort], Sort), DomainFun, DomainFun] with GenericFunctionCompanion[DomainFun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = createIfNonExistent((id, argSorts, resultSort))

  override def actualCreate(args: (Identifier, Seq[Sort], Sort)): DomainFun = new DomainFun(args._1, args._2, args._3)
}

class SMTFun private[terms] (val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort)
  extends ConditionalFlyweight[(Identifier, Seq[Sort], Sort), SMTFun] with GenericFunction[SMTFun] {

  def copy(id: Identifier = id, argSorts: Seq[Sort] = argSorts, resultSort: Sort = resultSort) =
   SMTFun(id, argSorts, resultSort)
}

object SMTFun extends CondFlyweightFactory[(Identifier, Seq[Sort], Sort), SMTFun, SMTFun] with GenericFunctionCompanion[SMTFun] {
  def apply(id: Identifier, argSorts: Seq[Sort], resultSort: Sort) = createIfNonExistent((id, argSorts, resultSort))

  override def actualCreate(args: (Identifier, Seq[Sort], Sort)): SMTFun = new SMTFun(args._1, args._2, args._3)
}

class Macro private[terms] (val id: Identifier, val argSorts: Seq[Sort], val resultSort: Sort) extends Applicable
  with ConditionalFlyweight[(Identifier, Seq[Sort], Sort), Macro] {
  override val equalityDefiningMembers: (Identifier, Seq[Sort], Sort) = (id, argSorts, resultSort)
}

object Macro extends CondFlyweightFactory[(Identifier, Seq[Sort], Sort), Macro, Macro] {
  override def actualCreate(args: (Identifier, Stack[Sort], Sort)): Macro = new Macro(args._1, args._2, args._3)
}

class Var private[terms] (val id: Identifier, val sort: Sort, val isWildcard: Boolean) extends Function with Application[Var] with ConditionalFlyweight[(Identifier, Sort, Boolean), Var] {
  override val equalityDefiningMembers: (Identifier, Sort, Boolean) = (id, sort, isWildcard)
  val applicable: Var = this
  val args: Seq[Term] = Seq.empty
  val argSorts: Seq[Sort] = Seq(sorts.Unit)
  val resultSort: Sort = sort

  override lazy val toString = id.toString

  def copy(id: Identifier = id, sort: Sort = sort, isWildcard: Boolean = isWildcard) = Var(id, sort, isWildcard)
}

object Var extends CondFlyweightFactory[(Identifier, Sort, Boolean), Var, Var] {
  override def actualCreate(args: (Identifier, Sort, Boolean)): Var = new Var(args._1, args._2, args._3)
}

class App private[terms] (val applicable: Applicable, val args: Seq[Term])
    extends Application[Applicable]
       with ConditionalFlyweight[(Applicable, Seq[Term]), App] {
       /*with PossibleTrigger*/

  utils.assertExpectedSorts(applicable, args)

  val sort: Sort = applicable.resultSort
  val equalityDefiningMembers = (applicable, args)
  def copy(applicable: Applicable = applicable, args: Seq[Term] = args) = App(applicable, args)

  override lazy val toString =
    if (args.isEmpty) applicable.id.toString
    else s"${applicable.id}${args.mkString("(", ", ", ")")}"
}

object App extends CondFlyweightTermFactory[(Applicable, Seq[Term]), App] {
  def apply(applicable: Applicable, args: Seq[Term]) = createIfNonExistent((applicable, args))
  def apply(applicable: Applicable, arg: Term) = createIfNonExistent((applicable, Seq(arg)))

  override def actualCreate(args: (Applicable, Seq[Term])): App = new App(args._1, args._2)
}

/*
 * Applicable without arguments, only to be used as a hint for quantified chunks.
 */
case class AppHint(applicable: Applicable) extends Term {
  val sort = applicable.resultSort
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

  /** @see [[ast.utility.Visitor.visit]] */
  def visit(f: PartialFunction[Term, Any]): Unit =
    ast.utility.Visitor.visit(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.visitOpt]] */
  def visitOpt(f: Term => Boolean): Unit =
    ast.utility.Visitor.visitOpt(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.reduceTree]] */
  def reduceTree[R](f: (Term, Seq[R]) => R): R =
    ast.utility.Visitor.reduceTree(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.existsDefined]] */
  def existsDefined(f: PartialFunction[Term, Any]): Boolean =
    ast.utility.Visitor.existsDefined(this, state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.hasSubnode]] */
  def hasSubterm(subterm: Term): Boolean =
    ast.utility.Visitor.hasSubnode(this, subterm, state.utils.subterms)

  /** @see [[ast.utility.Visitor.deepCollect]] */
  def deepCollect[R](f: PartialFunction[Term, R]) : Seq[R] =
    ast.utility.Visitor.deepCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.shallowCollect]] */
  def shallowCollect[R](f: PartialFunction[Term, R]): Seq[R] =
    ast.utility.Visitor.shallowCollect(Seq(this), state.utils.subterms)(f)

  /** @see [[ast.utility.Visitor.find]] */
  def find[R](f: PartialFunction[Term, R]): Option[R] =
    ast.utility.Visitor.find(this, state.utils.subterms)(f)

  /** @see [[state.utils.transform]] */
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

/**
  * Trait that implements equality and hashCode based on the equality of the equalityDefiningMembers value.
  * Used to implement case class like behavior for ordinary classes.
  * No longer used and superseded by the ConditionalFlyweight trait, but kept here for documentation purposes.
  */
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

/**
  * A trait that defines equality and hashcode in such a way that:
  * 1. if Verifier.config.useFlyweight is set, then both are computed using references
  * 2. otherwise, both are computed based on equality of the equalityDefiningMembers value.
  * See also trait StructuralEquality above.
  * The motivation for this is to use the flyweight pattern when Z3 is used via its API, in which case it is
  * advantageous to have only a single version of each Silicon term (since this enables check caching of their
  * Z3 translations, and repeatedly translating the same Silicon term to a Z3 expression massively reduces performance
  * for large files), but to avoid the overhead of the flyweight pattern otherwise (since it costs time to check
  * for existing copies of a term, and there is no benefit to this when Z3 or some other SMT solver is used via
  * StdIO.
  *
  * @tparam T the type of the constructor parameters of the class (i.e., a tuple or a single parameter type)
  * @tparam V the type of the class implementing the trait
  */
trait ConditionalFlyweight[T, V] { self: AnyRef =>
  // The single value or tuple of values that define equality
  val equalityDefiningMembers: T

  override lazy val hashCode = if (Verifier.config.useFlyweight)
    System.identityHashCode(this)
  else
    viper.silver.utility.Common.generateHashCode(equalityDefiningMembers)

  override def equals(other: Any): Boolean = {
    if (Verifier.config.useFlyweight) {
      this.eq(other.asInstanceOf[AnyRef])
    } else {
      (
        this.eq(other.asInstanceOf[AnyRef])
          || (other match {
          case se: ConditionalFlyweight[T, V] if this.getClass.eq(se.getClass) =>
            equalityDefiningMembers == se.equalityDefiningMembers
          case _ => false
        }))
    }
  }

  override lazy val toString: String = {
    val argString = equalityDefiningMembers match {
      case p: Product =>
        p.productIterator.mkString(", ")
      case trm => trm.toString
    }
    s"${this.getClass.getSimpleName}(${argString})"
  }
}

trait ConditionalFlyweightBinaryOp[T] extends ConditionalFlyweight[(Term, Term), T] with BinaryOp[Term] with Term {
  override val equalityDefiningMembers = (p0,  p1)
}

trait ConditionalFlyweightUnaryOp[T] extends ConditionalFlyweight[Term, T] with UnaryOp[Term] with Term {
  override val equalityDefiningMembers = p
}

/**
  * Version of CondFlyweightFactory where the return type of apply is Term, i.e., the apply method may return
  * arbitrary terms due to simplification.
  * @tparam T constructor argument type of the class V (i.e., a tuple or the type of the only argument)
  * @tparam V class we are creating instances of
  */
trait CondFlyweightTermFactory[T, V <: ConditionalFlyweight[T, V] with Term] extends CondFlyweightFactory[T, Term, V]

/**
  * Version of CondFlyweightFactory where the return type of apply is V, i.e., the apply method always returns an
  * instance of the class whose apply method is called.
  * @tparam T constructor argument type of the class V (i.e., a tuple or the type of the only argument)
  * @tparam V class we are creating instances of
  */
trait PreciseCondFlyweightFactory[T, V <: ConditionalFlyweight[T, V] with Term] extends CondFlyweightFactory[T, V, V]


/**
  * Default version of GeneralCondFlyweightFactory where the arguments of the apply method is the same as the
  * constructor arguments of class V.
  * @tparam T constructor argument type of the class V (i.e., a tuple or the type of the only argument)
  * @tparam U return type of the apply method (i.e., either the class itself or something more general for simplifying
  *           apply methods)
  * @tparam V class we are creating instances of
  */
trait CondFlyweightFactory[T, U, V <: U with ConditionalFlyweight[T, V]] extends GeneralCondFlyweightFactory[T, T, U, V] {
  def apply(v1: T): U = createIfNonExistent(v1)

}

/**
  * Most general trait to be implemented by companion objects to create instances of ConditionalFlyweight[T, V].
  * @tparam IF parameter type of the apply method (can be different from the constructor args of the class)
  * @tparam T constructor argument type of the class V (i.e., a tuple or the type of the only argument)
  * @tparam U return type of the apply method (i.e., either the class itself or something more general for simplifying
  *           apply methods)
  * @tparam V class we are creating instances of
  */
trait GeneralCondFlyweightFactory[IF, T <: IF, U, V <: U with ConditionalFlyweight[T, V]] extends (IF => U) {

  var pool = new TrieMap[T, V]()

  def createIfNonExistent(args: T): V = {
    if (Verifier.config.useFlyweight) {
      pool.getOrElseUpdate(args, actualCreate(args))
    } else {
      actualCreate(args)
    }
  }

  def unapply(v: V): Option[T] = Some(v.equalityDefiningMembers)

  def actualCreate(args: T): V
}


/* Literals */

sealed trait Literal extends Term

case object Unit extends SnapshotTerm with Literal {
  override lazy val toString = "_"
}

class IntLiteral private[terms] (val n: BigInt) extends ArithmeticTerm with Literal with ConditionalFlyweight[BigInt, IntLiteral] {
  def +(m: Int) = IntLiteral(n + m)
  def -(m: Int) = IntLiteral(n - m)
  def *(m: Int) = IntLiteral(n * m)
  def /(m: Int) = Div(this, IntLiteral(m))
  override lazy val toString = n.toString()
  override val equalityDefiningMembers: BigInt = n
}
object IntLiteral extends CondFlyweightFactory[BigInt, IntLiteral, IntLiteral] {
  override def actualCreate(args: BigInt): IntLiteral = new IntLiteral(args)
}

case object Null extends Term with Literal {
  val sort = sorts.Ref
  override lazy val toString = "Null"
}

sealed trait BooleanLiteral extends BooleanTerm with Literal {
  def value: Boolean
  override lazy val toString = value.toString
}

object BooleanLiteral extends (Boolean => BooleanLiteral) {
  def apply(b: Boolean): BooleanLiteral = if (b) True else False
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

  private val qidCounter = new AtomicInteger()

  def defaultName = s"quant-u-${qidCounter.getAndIncrement()}"

  def apply(qvar: Var, tBody: Term, trigger: Trigger): Quantification =
    apply(qvar, tBody, trigger, defaultName)

  def apply(qvar: Var, tBody: Term, trigger: Trigger, name: String) =
    Quantification(Forall, qvar :: Nil, tBody, trigger :: Nil, name)

  def apply(qvar: Var, tBody: Term, trigger: Trigger, name: String, isGlobal: Boolean) =
    Quantification(Forall, qvar :: Nil, tBody, trigger :: Nil, name, isGlobal)

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(qvar, tBody, triggers, defaultName)

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger], name: String) =
    Quantification(Forall, qvar :: Nil, tBody, triggers, name)

  def apply(qvar: Var, tBody: Term, triggers: Seq[Trigger], name: String, isGlobal: Boolean) =
    Quantification(Forall, qvar :: Nil, tBody, triggers, name, isGlobal)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger): Quantification =
    apply(qvars, tBody, trigger, defaultName)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger, name: String) =
    Quantification(Forall, qvars, tBody, trigger :: Nil, name)

  def apply(qvars: Seq[Var], tBody: Term, trigger: Trigger, name: String, isGlobal: Boolean) =
    Quantification(Forall, qvars, tBody, trigger :: Nil, name, isGlobal)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(qvars, tBody, triggers, defaultName)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String) =
    Quantification(Forall, qvars, tBody, triggers, name)

  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String, isGlobal: Boolean) =
    Quantification(Forall, qvars, tBody, triggers, name, isGlobal)

  def unapply(q: Quantification): Some[(Seq[Var], Term, Seq[Trigger], String, Boolean)] =
    Some(q.vars, q.body, q.triggers, q.name, q.isGlobal)

  override lazy val toString = "QA"
}

object SimplifyingForall {
  def apply(qvars: Seq[Var], tBody: Term, triggers: Seq[Trigger]): Term = tBody match {
    case True => True
    case False if qvars.nonEmpty =>
      // This assumes that every sort is non-empty, which should be a safe assumption, since otherwise, declaring a
      // variable of that sort would also already be unsound.
      False
    case _ =>
      if (qvars.isEmpty) {
        tBody
      } else {
        Forall(qvars, tBody, triggers)
      }
  }
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

class Quantification private[terms] (val q: Quantifier, /* TODO: Rename */
                                     val vars: Seq[Var],
                                     val body: Term,
                                     val triggers: Seq[Trigger],
                                     val name: String,
                                     val isGlobal: Boolean,
                                     val weight: Option[Int])
    extends BooleanTerm
       with ConditionalFlyweight[(Quantifier, Seq[Var], Term, Seq[Trigger], String, Boolean, Option[Int]), Quantification] {

  val equalityDefiningMembers = (q, vars, body, triggers, name, isGlobal, weight)

  def copy(q: Quantifier = q,
           vars: Seq[Var] = vars,
           body: Term = body,
           triggers: Seq[Trigger] = triggers,
           name: String = name,
           isGlobal: Boolean = isGlobal,
           weight: Option[Int] = weight) = {

    Quantification(q, vars, body, triggers, name, isGlobal, weight)
  }

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
    extends CondFlyweightTermFactory[(Quantifier, Seq[Var], Term, Seq[Trigger], String, Boolean, Option[Int]), Quantification] {

  private val qidCounter = new AtomicInteger()

  def transformSeqTerms(t: Trigger): Seq[Trigger] = {
    val transformed = Trigger(t.p.map(_.transform{
      case SeqIn(t0, t1) => SeqInTrigger(t0, t1)
    }()))
    if (transformed != t)
      Seq(t, transformed)
    else
      Seq(t)
  }

  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger]): Quantification =
    apply(q, vars, tBody, triggers, s"quant-${qidCounter.getAndIncrement()}")

  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String)
  : Quantification = {

    apply(q, vars, tBody, triggers, name, false)
  }

  def apply(q: Quantifier, vars: Seq[Var], tBody: Term, triggers: Seq[Trigger], name: String, weight: Option[Int])
  : Quantification = {

    apply(q, vars, tBody, triggers, name, false, weight)
  }

  def apply(q: Quantifier,
            vars: Seq[Var],
            tBody: Term,
            triggers: Seq[Trigger],
            name: String,
            isGlobal: Boolean)
  : Quantification = {
    apply(q, vars, tBody, triggers, name, isGlobal, None)
  }

  def apply(q: Quantifier,
            vars: Seq[Var],
            tBody: Term,
            triggers: Seq[Trigger],
            name: String,
            isGlobal: Boolean,
            weight: Option[Int])
           : Quantification = {

    val rewrittenTriggers = if (Verifier.config.useOldAxiomatization()) triggers else triggers.flatMap(transformSeqTerms(_))

//    assert(vars.nonEmpty, s"Cannot construct quantifier $q with no quantified variable")
//    assert(vars.distinct.length == vars.length, s"Found duplicate vars: $vars")
//    assert(triggers.distinct.length == triggers.length, s"Found duplicate triggers: $triggers")

    /* TODO: If we optimise away a quantifier, we cannot, for example, access
     *       autoTrigger on the returned object.
     */
    createIfNonExistent(q, vars, tBody, rewrittenTriggers, name, isGlobal, weight)
//    tBody match {
//    case True | False => tBody
//    case _ => new Quantification(q, vars, tBody, triggers)
//  }
  }

  override def actualCreate(args: (Quantifier, Seq[Var], Term, Seq[Trigger], String, Boolean, Option[Int])): Quantification = {
    new Quantification(args._1, args._2, args._3, args._4, args._5, args._6, args._7)
  }
}

/* Arithmetic expression terms */

sealed abstract class ArithmeticTerm extends Term {
  val sort = sorts.Int
}

class Plus(val p0: Term, val p1: Term) extends ArithmeticTerm
    with ConditionalFlyweightBinaryOp[Plus] {

  override val op = "+"
}

object Plus extends CondFlyweightTermFactory[(Term, Term), Plus] {
  import predef.Zero

  override def apply(v0: (Term, Term)) = v0 match {
    case (t0, Zero) => t0
    case (Zero, t1) => t1
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 + n1)
    case (e0, e1) => createIfNonExistent(e0, e1)
  }

  override def actualCreate(args: (Term, Term)): Plus = new Plus(args._1, args._2)
}

class Minus(val p0: Term, val p1: Term) extends ArithmeticTerm
  with ConditionalFlyweightBinaryOp[Minus] {

  override val op = "-"
}

object Minus extends CondFlyweightTermFactory[(Term, Term), Minus] {
  import predef.Zero

  override def apply(v1: (Term, Term)) = v1 match {
    case (t0, Zero) => t0
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 - n1)
    case (t0, t1) if t0 == t1 => Zero
    case (e0, e1) => createIfNonExistent(e0, e1)
  }

  override def actualCreate(args: (Term, Term)): Minus = new Minus(args._1, args._2)
}

class Times(val p0: Term, val p1: Term) extends ArithmeticTerm
    with ConditionalFlyweightBinaryOp[Times] {

  override val op = "*"
}

object Times extends CondFlyweightTermFactory[(Term, Term), Times] {
  import predef.{Zero, One}

  override def apply(v0: (Term, Term)) =v0 match {
    case (_, Zero) => Zero
    case (Zero, _) => Zero
    case (t0, One) => t0
    case (One, t1) => t1
    case (IntLiteral(n0), IntLiteral(n1)) => IntLiteral(n0 * n1)
    case (e0, e1) => createIfNonExistent(e0, e1)
  }

  override def actualCreate(args: (Term, Term)): Times = new Times(args._1, args._2)
}

class Div(val p0: Term, val p1: Term) extends ArithmeticTerm
    with ConditionalFlyweightBinaryOp[Div] {

  override val op = "/"
}

object Div extends CondFlyweightFactory[(Term, Term), Div, Div] {
  override def actualCreate(args: (Term, Term)): Div = new Div(args._1, args._2)
}

class Mod(val p0: Term, val p1: Term) extends ArithmeticTerm
    with ConditionalFlyweightBinaryOp[Mod] {

  override val op = "%"
}

object Mod extends CondFlyweightFactory[(Term, Term), Mod, Mod] {
  override def actualCreate(args: (Term, Term)): Mod = new Mod(args._1, args._2)
}


/* Boolean expression terms */

sealed trait BooleanTerm extends Term { override val sort = sorts.Bool }

class Not(val p: Term) extends BooleanTerm
    with ConditionalFlyweightUnaryOp[Not] {
  assert(p.sort == sorts.Bool)
  override val op = "!"

  override lazy val toString = p match {
    case eq: BuiltinEquals => s"${eq.p0.toString} != ${eq.p1.toString}"
    case _ => s"!($p)"
  }
}

object Not extends CondFlyweightTermFactory[Term, Not] {

  override def apply(e0: Term) = e0 match {
    case Not(e1) => e1
    case True => False
    case False => True
    case _ => createIfNonExistent(e0)
  }
  override def actualCreate(args: Term): Not = new Not(args)
}

class Or private[terms] (val ts: Seq[Term]) extends BooleanTerm
    with ConditionalFlyweight[Seq[Term], Or] {

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
object Or extends GeneralCondFlyweightFactory[Iterable[Term], Seq[Term], Term, Or] {
  def apply(ts: Term*) = createOr(ts)
  def apply(ts: Iterable[Term]) = createOr(ts.toSeq)



  //  def apply(e0: Term, e1: Term) = (e0, e1) match {
  //    case (True, _) | (_, True) => True
  //    case (False, _) => e1
  //    case (_, False) => e0
  //    case _ if e0 == e1 => e0
  //    case _ => new Or(e0, e1)
  //  }

  @inline
  def createOr(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case Or(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == False)
    ts = ts.distinct

    ts match {
      case Seq() => False
      case Seq(t) => t
      case _ if ts.contains(True) => True
      case _ => createIfNonExistent(ts)
    }
  }

  override def actualCreate(args: Seq[Term]): Or = new Or(args)
}

class And private[terms](val ts: Seq[Term]) extends BooleanTerm
    with ConditionalFlyweight[Seq[Term], And] {

  assert(ts.nonEmpty, "Expected at least one term, but found none")

  val equalityDefiningMembers = ts

  override lazy val toString = ts.mkString(" && ")
}

object And extends GeneralCondFlyweightFactory[Iterable[Term], Seq[Term], Term, And] {
  def apply(ts: Term*) = createAnd(ts)
  def apply(ts: Iterable[Term]) = createAnd(ts.toSeq)

  @inline
  def createAnd(_ts: Seq[Term]): Term = {
    var ts = _ts.flatMap { case And(ts1) => ts1; case other => other :: Nil}
    ts = _ts.filterNot(_ == True)
    ts = ts.distinct

    ts match {
      case Seq() => True
      case Seq(t) => t
      case _ if ts.contains(False) => False
      case _ => createIfNonExistent(ts)
    }
  }

  override def actualCreate(args: Seq[Term]): And = new And(args)
}

class Implies(val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[Implies] {

  override val op = "==>"
}

object Implies extends CondFlyweightTermFactory[(Term, Term), Implies] {
  @tailrec
  override def apply(v0: (Term, Term)): Term = v0 match {
    case (True, e1) => e1
    case (False, _) => True
    case (_, True) => True
    case (e0, Implies(e10, e11)) => Implies(And(e0, e10), e11)
    case (e0, e1) if e0 == e1 => True
    case (e0, e1) => createIfNonExistent(e0, e1)
  }

  override def actualCreate(args: (Term, Term)): Implies = new Implies(args._1, args._2)
}

class Iff(val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[Iff] {

  override val op = "<==>"
}

object Iff extends CondFlyweightTermFactory[(Term, Term), Iff] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (True, e1) => e1
    case (e0, True) => e0
    case (e0, e1) if e0 == e1 => True
    case (e0, e1) => createIfNonExistent(e0, e1)
  }

  override def actualCreate(args: (Term, Term)): Iff = new Iff(args._1, args._2)
}

class Ite private[terms] (val t0: Term, val t1: Term, val t2: Term)
    extends Term with ConditionalFlyweight[(Term, Term, Term), Ite] {

  assert(t0.sort == sorts.Bool && t1.sort == t2.sort, /* @elidable */
         s"Ite term Ite($t0, $t1, $t2) is not well-sorted: ${t0.sort}, ${t1.sort}, ${t2.sort}")

  val equalityDefiningMembers = (t0, t1, t2)
  val sort = t1.sort
  override lazy val toString = s"($t0 ? $t1 : $t2)"
}

object Ite extends CondFlyweightTermFactory[(Term, Term, Term), Ite] {
  override def apply(v0: (Term, Term, Term)) = v0 match {
    case (_, e1, e2) if e1 == e2 => e1
    case (True, e1, _) => e1
    case (False, _, e2) => e2
    case (e0, True, False) => e0
    case (e0, False, True) => Not(e0)
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term, Term)): Ite = new Ite(args._1, args._2, args._3)
}

/* Comparison expression terms */

sealed trait ComparisonTerm extends BooleanTerm

sealed trait Equals extends ComparisonTerm with BinaryOp[Term] { override val op = "==" }

object Equals extends ((Term, Term) => BooleanTerm) {
  def apply(e0: Term, e1: Term) = {
    assert(e0.sort == e1.sort,
           s"Expected both operands to be of the same sort, but found ${e0.sort} ($e0) and ${e1.sort} ($e1).")

    // Note that the syntactic simplifications (first two cases) can interfere with triggering
    // if they eliminate potential trigger terms.
    (e0, e1) match {
      case (`e0`, `e0`) => True
      case (l1: Literal, l2: Literal) => BooleanLiteral(l1 == l2)
      case _ =>
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
  }

  def unapply(e: Equals) = Some((e.p0, e.p1))
}

/* Represents built-in equality, e.g., '=' in SMT-LIB */
class BuiltinEquals private[terms] (val p0: Term, val p1: Term) extends ConditionalFlyweightBinaryOp[BuiltinEquals] with Equals

object BuiltinEquals extends CondFlyweightFactory[(Term, Term), BooleanTerm, BuiltinEquals] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (v0: Var, v1: Var) if v0 == v1 => True
    case (p0: PermLiteral, p1: PermLiteral) =>
      // NOTE: The else-case (False) is only justified because permission literals are stored in a normal form
      // such that two literals are semantically equivalent iff they are syntactically equivalent.
      if (p0.literal == p1.literal) True else False
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): BuiltinEquals = new BuiltinEquals(args._1, args._2)
}

/* Custom equality that (potentially) needs to be axiomatised. */
class CustomEquals private[terms] (val p0: Term, val p1: Term) extends ConditionalFlyweightBinaryOp[CustomEquals] with Equals {

  override val op = "==="
}

object CustomEquals extends CondFlyweightFactory[(Term, Term), BooleanTerm, CustomEquals] {
  override def actualCreate(args: (Term, Term)): CustomEquals = new CustomEquals(args._1, args._2)
}

class Less private[terms] (val p0: Term, val p1: Term) extends ComparisonTerm
    with ConditionalFlyweightBinaryOp[Less] {

  assert(p0.sort == p1.sort,
         s"Expected both operands to be of the same sort, but found ${p0.sort} ($p0) and ${p1.sort} ($p1).")

  override val op = "<"
}

object Less extends /* OptimisingBinaryArithmeticOperation with */ CondFlyweightTermFactory[(Term, Term), Less] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 < n1) True else False
    case (pl0: PermLiteral, pl1: PermLiteral) => if (pl0.literal < pl1.literal) True else False
    case (t0, t1) if t0 == t1 => False
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): Less = new Less(args._1, args._2)
}

class AtMost private[terms] (val p0: Term, val p1: Term) extends ComparisonTerm
    with ConditionalFlyweightBinaryOp[AtMost] {

  override val op = "<="
}

object AtMost extends /* OptimisingBinaryArithmeticOperation with */ CondFlyweightTermFactory[(Term, Term), AtMost] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 <= n1) True else False
    case (pl0: PermLiteral, pl1: PermLiteral) => if (pl0.literal <= pl1.literal) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): AtMost = new AtMost(args._1, args._2)
}

class Greater private[terms] (val p0: Term, val p1: Term) extends ComparisonTerm
    with ConditionalFlyweightBinaryOp[Greater] {

  override val op = ">"
}

object Greater extends /* OptimisingBinaryArithmeticOperation with */ CondFlyweightTermFactory[(Term, Term), Greater] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 > n1) True else False
    case (pl0: PermLiteral, pl1: PermLiteral) => if (pl0.literal > pl1.literal) True else False
    case (t0, t1) if t0 == t1 => False
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): Greater = new Greater(args._1, args._2)
}

class AtLeast private[terms] (val p0: Term, val p1: Term) extends ComparisonTerm
    with ConditionalFlyweightBinaryOp[AtLeast] {

  override val op = ">="
}

object AtLeast extends /* OptimisingBinaryArithmeticOperation with */ CondFlyweightTermFactory[(Term, Term), AtLeast] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (IntLiteral(n0), IntLiteral(n1)) => if (n0 >= n1) True else False
    case (pl0: PermLiteral, pl1: PermLiteral) => if (pl0.literal >= pl1.literal) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): AtLeast = new AtLeast(args._1, args._2)
}

/*
 * Permissions
 */

sealed trait Permissions extends Term {
  val sort = sorts.Perm
}

sealed abstract class PermLiteral(val literal: Rational) extends Permissions

case object NoPerm extends PermLiteral(Rational.zero) { override lazy val toString = "Z" }
case object FullPerm extends PermLiteral(Rational.one) { override lazy val toString = "W" }

class FractionPermLiteral private[terms] (r: Rational) extends PermLiteral(r) with ConditionalFlyweight[Rational, FractionPermLiteral] {
  override val equalityDefiningMembers: Rational = r
  override lazy val toString = literal.toString
}

object FractionPermLiteral extends CondFlyweightFactory[Rational, Permissions, FractionPermLiteral] {
  override def apply(r: Rational) = r match {
    case Rational(n, _) if n == 0 => NoPerm
    case Rational(n, d) if n == d => FullPerm
    case _ => createIfNonExistent(r)
  }

  override def actualCreate(args: Rational): FractionPermLiteral = new FractionPermLiteral(args)
}

class FractionPerm private[terms] (val n: Term, val d: Term)
    extends Permissions
       with ConditionalFlyweight[(Term, Term), FractionPerm] {

  val equalityDefiningMembers = (n, d)
  override lazy val toString = s"$n/$d"
}

object FractionPerm extends CondFlyweightFactory[(Term, Term), Permissions, FractionPerm] {
  override def apply(v: (Term, Term)) = v match {
    case (IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => FractionPermLiteral(Rational(i1, i2))
    case _ => createIfNonExistent(v)
  }

  override def actualCreate(args: (Term, Term)): FractionPerm = new FractionPerm(args._1, args._2)
}

class IsValidPermVal private[terms] (val t: Term) extends BooleanTerm with ConditionalFlyweight[Term, IsValidPermVal] {
  override val equalityDefiningMembers: Term = t
  override lazy val toString = s"PVal($t)"
}

object IsValidPermVal extends CondFlyweightTermFactory[Term, IsValidPermVal] {
  override def actualCreate(args: Term): IsValidPermVal = new IsValidPermVal((args))
}

class IsReadPermVar private[terms] (val v: Var) extends BooleanTerm with ConditionalFlyweight[Var, IsReadPermVar] {
  override val equalityDefiningMembers: Var = v
  override lazy val toString = s"RdVar($v)"
}

object IsReadPermVar extends CondFlyweightTermFactory[Var, IsReadPermVar] {
  override def actualCreate(args: Var): IsReadPermVar = new IsReadPermVar((args))
}

class PermTimes private[terms] (val p0: Term, val p1: Term)
    extends Permissions
       with ConditionalFlyweightBinaryOp[PermTimes] {

  override val op = "*"
}

object WildcardSimplifyingPermTimes extends ((Term, Term) => Term) {
  override def apply(t0: Term, t1: Term) = (t0, t1) match {
    case (v1: Var, v2: Var) if v1.isWildcard && v2.isWildcard => if (v1.id.name.compareTo(v2.id.name) > 0) v1 else v2
    case (v1: Var, pl: PermLiteral) if v1.isWildcard && pl.literal > Rational.zero => v1
    case (pl: PermLiteral, v2: Var) if v2.isWildcard && pl.literal > Rational.zero => v2
    case (Ite(c, t1, t2), t3) => Ite(c, WildcardSimplifyingPermTimes(t1, t3), WildcardSimplifyingPermTimes(t2, t3))
    case (PermPlus(t1, t2), t3) => PermPlus(WildcardSimplifyingPermTimes(t1, t3), WildcardSimplifyingPermTimes(t2, t3))
    case (t1, PermPlus(t2, t3)) => PermPlus(WildcardSimplifyingPermTimes(t1, t2), WildcardSimplifyingPermTimes(t1, t3))
    case (PermMinus(t1, t2), t3) => PermMinus(WildcardSimplifyingPermTimes(t1, t3), WildcardSimplifyingPermTimes(t2, t3))
    case (t1, PermMinus(t2, t3)) => PermMinus(WildcardSimplifyingPermTimes(t1, t2), WildcardSimplifyingPermTimes(t1, t3))
    case (t1, Ite(c, t2, t3)) => Ite(c, WildcardSimplifyingPermTimes(t1, t2), WildcardSimplifyingPermTimes(t1, t3))
    case _ => PermTimes(t0, t1)
  }
}

object PermTimes extends CondFlyweightTermFactory[(Term, Term), PermTimes] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (FullPerm, t) => t
    case (t, FullPerm) => t
    case (NoPerm, _) => NoPerm
    case (_, NoPerm) => NoPerm
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal * p1.literal)
    case (Ite(c, t1, t2), t3) => Ite(c, PermTimes(t1, t3), PermTimes(t2, t3))
    case (PermPlus(t1, t2), t3) => PermPlus(PermTimes(t1, t3), PermTimes(t2, t3))
    case (t1, PermPlus(t2, t3)) => PermPlus(PermTimes(t1, t2), PermTimes(t1, t3))
    case (PermMinus(t1, t2), t3) => PermMinus(PermTimes(t1, t3), PermTimes(t2, t3))
    case (t1, PermMinus(t2, t3)) => PermMinus(PermTimes(t1, t2), PermTimes(t1, t3))
    case (t1, Ite(c, t2, t3)) => Ite(c, PermTimes(t1, t2), PermTimes(t1, t3))
    case (_, _) => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermTimes = new PermTimes(args._1, args._2)
}

class IntPermTimes private[terms] (val p0: Term, val p1: Term)
    extends ConditionalFlyweightBinaryOp[IntPermTimes]
      with Permissions
      with BinaryOp[Term] {

  override val op = "*"
}

object IntPermTimes extends CondFlyweightTermFactory[(Term, Term), IntPermTimes] {
  import predef.{Zero, One}

  override def apply(v0: (Term, Term)) = v0 match {
    case (Zero, _) => NoPerm
    case (One, t) => t
    case (_, NoPerm) => NoPerm
    case (IntLiteral(i), p: PermLiteral) => FractionPermLiteral(Rational(i, 1) * p.literal)
    case (_, _) => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): IntPermTimes = new IntPermTimes(args._1, args._2)
}

class PermIntDiv private[terms] (val p0: Term, val p1: Term)
    extends ConditionalFlyweightBinaryOp[PermIntDiv]
      with Permissions
      with BinaryOp[Term] {

  utils.assertSort(p1, "Second term", sorts.Int)

  override val op = "/"
}

object PermIntDiv extends CondFlyweightTermFactory[(Term, Term), PermIntDiv] {
  import predef.One

  override def apply(v0: (Term, Term)) = v0 match {
    case (t, One) => t
    case (p: PermLiteral, IntLiteral(i)) if i != 0 => FractionPermLiteral(p.literal / Rational(i, 1))
    case (_, _) => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermIntDiv = new PermIntDiv(args._1, args._2)
}

class PermPermDiv private[terms] (val p0: Term, val p1: Term)
  extends ConditionalFlyweightBinaryOp[PermPermDiv]
    with Permissions
    with BinaryOp[Term] {

  utils.assertSort(p1, "Second term", sorts.Perm)

  override val op = "/"
}

object PermPermDiv extends CondFlyweightTermFactory[(Term, Term), PermPermDiv] {

  override def actualCreate(args: (Term, Term)): PermPermDiv = new PermPermDiv(args._1, args._2)
}

object PermDiv extends ((Term, Term) => Term) {
  import predef.One

  def apply(t0: Term, t1: Term) = PermTimes(t0, FractionPerm(One, t1))
}

class PermPlus private[terms] (val p0: Term, val p1: Term)
    extends ConditionalFlyweightBinaryOp[PermPlus]
      with Permissions
      with BinaryOp[Term] {

  override val op = "+"
}

object PermPlus extends CondFlyweightTermFactory[(Term, Term), PermPlus] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (NoPerm, t1) => t1
    case (t0, NoPerm) => t0
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal + p1.literal)
    case (FractionPerm(n1, d1), FractionPerm(n2, d2)) if d1 == d2 => FractionPerm(Plus(n1, n2), d1)
    case (PermMinus(t00, t01), t1) if t01 == t1 => t00
    case (t0, PermMinus(t10, t11)) if t11 == t0 => t10

    case (_, _) => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermPlus = new PermPlus(args._1, args._2)
}

class PermMinus private[terms] (val p0: Term, val p1: Term)
    extends Permissions
       with BinaryOp[Term]
       with ConditionalFlyweightBinaryOp[PermMinus] {

  override val op = "-"

  override lazy val toString = p1 match {
    case _: BinaryOp[_] => s"$p0 $op ($p1)"
    case _ => s"$p0 $op $p1"
  }
}

object PermMinus extends CondFlyweightTermFactory[(Term, Term), PermMinus] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (t0, NoPerm) => t0
    case (p0, p1) if p0 == p1 => NoPerm
    case (p0: PermLiteral, p1: PermLiteral) => FractionPermLiteral(p0.literal - p1.literal)
    case (p0, PermMinus(p1, p2)) if p0 == p1 => p2
    case (PermPlus(p0, p1), p2) if p0 == p2 => p1
    case (PermPlus(p0, p1), p2) if p1 == p2 => p0
    case (_, _) => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermMinus = new PermMinus(args._1, args._2)
}

class PermLess private[terms] (val p0: Term, val p1: Term)
    extends BooleanTerm
       with BinaryOp[Term]
       with ConditionalFlyweightBinaryOp[PermLess] {

  override lazy val toString = s"($p0) < ($p1)"

  override val op = "<"
}

object PermLess extends CondFlyweightTermFactory[(Term, Term), PermLess] {
  override def apply(v0: (Term, Term)): Term = {
    v0 match {
      case (t0, t1) if t0 == t1 => False
      case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal < p1.literal) True else False

      case (t0, Ite(tCond, tIf, tElse)) =>
        /* The pattern p0 < b ? p1 : p2 arises very often in the context of quantified permissions.
         * Pushing the comparisons into the ite allows further simplifications.
         */
        Ite(tCond, PermLess(t0, tIf), PermLess(t0, tElse))

      case _ => createIfNonExistent(v0)
    }
  }

  override def actualCreate(args: (Term, Term)): PermLess = new PermLess(args._1, args._2)
}

class PermAtMost private[terms] (val p0: Term, val p1: Term) extends ComparisonTerm
    with ConditionalFlyweightBinaryOp[PermAtMost] {

  override val op = "<="
}

object PermAtMost extends CondFlyweightTermFactory[(Term, Term), PermAtMost] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal <= p1.literal) True else False
    case (t0, t1) if t0 == t1 => True
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermAtMost = new PermAtMost(args._1, args._2)
}

class PermMin private[terms] (val p0: Term, val p1: Term) extends Permissions
    with BinaryOp[Term]
    with ConditionalFlyweightBinaryOp[PermMin] {

  utils.assertSort(p0, "Permission 1st", sorts.Perm)
  utils.assertSort(p1, "Permission 2nd", sorts.Perm)

  override lazy val toString = s"min ($p0, $p1)"
}

object PermMin extends CondFlyweightTermFactory[(Term, Term), PermMin] {
  override def apply(v0: (Term, Term)) = v0 match {
    case (t0, t1) if t0 == t1 => t0
    case (p0: PermLiteral, p1: PermLiteral) => if (p0.literal > p1.literal) p1 else p0
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): PermMin = new PermMin(args._1, args._2)
}

/* Sequences */

sealed trait SeqTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Seq
}

class SeqRanged private[terms] (val p0: Term, val p1: Term) extends SeqTerm /* with BinaryOp[Term] */
  with ConditionalFlyweight[(Term, Term), SeqRanged] {
  utils.assertSort(p0, "first operand", sorts.Int)
  utils.assertSort(p1, "second operand", sorts.Int)

  val elementsSort = sorts.Int
  val sort = sorts.Seq(elementsSort)

  override val equalityDefiningMembers: (Term, Term) = (p0, p1)

  override lazy val toString = s"[$p0..$p1]"
}

object SeqRanged extends CondFlyweightTermFactory[(Term, Term), SeqRanged] {
  override def actualCreate(args: (Term, Term)): SeqRanged = new SeqRanged(args._1, args._2)
}

class SeqNil private[terms] (val elementsSort: Sort) extends SeqTerm with Literal with ConditionalFlyweight[Sort, SeqNil] {
  val sort = sorts.Seq(elementsSort)
  override lazy val toString = "Nil"
  override val equalityDefiningMembers: Sort = elementsSort
}

object SeqNil extends CondFlyweightTermFactory[Sort, SeqNil] {
  override def actualCreate(args: Sort): SeqNil = new SeqNil(args)
}

class SeqSingleton private[terms] (val p: Term) extends SeqTerm /* with UnaryOp[Term] */ with ConditionalFlyweight[Term, SeqSingleton] {
  val elementsSort = p.sort
  val sort = sorts.Seq(elementsSort)
  override val equalityDefiningMembers: Term = p

  override lazy val toString = s"[$p]"
}

object SeqSingleton extends CondFlyweightFactory[Term, SeqTerm, SeqSingleton] {
  override def actualCreate(args: Term): SeqSingleton = new SeqSingleton(args)
}

class SeqAppend private[terms] (val p0: Term, val p1: Term) extends SeqTerm
    with ConditionalFlyweightBinaryOp[SeqAppend] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override val op = "++"
}

object SeqAppend extends CondFlyweightTermFactory[(Term, Term), SeqAppend] {
  override def apply(v0: (Term, Term)) = {
    utils.assertSameSorts[sorts.Seq](v0._1, v0._2)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqAppend = new SeqAppend(args._1, args._2)
}

class SeqDrop private[terms] (val p0: Term, val p1: Term) extends SeqTerm
    with ConditionalFlyweightBinaryOp[SeqDrop] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = p0.toString + "[" + p1.toString + ":]"
}

object SeqDrop extends CondFlyweightTermFactory[(Term, Term), SeqDrop] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqDrop = new SeqDrop(args._1, args._2)
}

class SeqTake private[terms] (val p0: Term, val p1: Term) extends SeqTerm
    with ConditionalFlyweightBinaryOp[SeqTake] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Seq].elementsSort
  val sort = sorts.Seq(elementsSort)

  override lazy val toString = p0.toString + "[:" + p1.toString + "]"
}

object SeqTake extends CondFlyweightTermFactory[(Term, Term), SeqTake] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqTake = new SeqTake(args._1, args._2)
}

class SeqLength private[terms] (val p: Term) extends Term
    with ConditionalFlyweightUnaryOp[SeqLength] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object SeqLength extends CondFlyweightTermFactory [Term, SeqLength] {
  override def apply(t: Term) = {
    utils.assertSort(t, "term", "Seq", _.isInstanceOf[sorts.Seq])
    createIfNonExistent(t)
  }

  override def actualCreate(args: Term): SeqLength = new SeqLength(args)
}

class SeqAt private[terms] (val p0: Term, val p1: Term) extends Term
    with ConditionalFlyweightBinaryOp[SeqAt] {

  val sort = p0.sort.asInstanceOf[sorts.Seq].elementsSort

  override lazy val toString = s"$p0[$p1]"
}

object SeqAt extends CondFlyweightTermFactory[(Term, Term), SeqAt] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqAt = new SeqAt(args._1, args._2)
}

class SeqIn private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[SeqIn] {

  override lazy val toString = s"$p1 in $p0"
}

object SeqIn extends CondFlyweightTermFactory[(Term, Term), SeqIn] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqIn = new SeqIn(args._1, args._2)
}

class SeqInTrigger private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
  with ConditionalFlyweightBinaryOp[SeqInTrigger] {

  override lazy val toString = s"$p1 in $p0"
}

object SeqInTrigger extends CondFlyweightTermFactory[(Term, Term), SeqInTrigger] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SeqInTrigger = new SeqInTrigger(args._1, args._2)
}

class SeqUpdate private[terms] (val t0: Term, val t1: Term, val t2: Term)
    extends SeqTerm
       with ConditionalFlyweight[(Term, Term, Term), SeqUpdate] {

  val sort = t0.sort.asInstanceOf[sorts.Seq]
  val elementsSort = sort.elementsSort
  val equalityDefiningMembers = (t0, t1, t2)
  override lazy val toString = s"$t0[$t1] := $t2"
}

object SeqUpdate extends CondFlyweightTermFactory[(Term, Term, Term), SeqUpdate] {
  override def apply(v0: (Term, Term, Term)) = {
    val (t0, t1, t2) = v0
    utils.assertSort(t0, "first operand", "Seq", _.isInstanceOf[sorts.Seq])
    utils.assertSort(t1, "second operand", sorts.Int)
    utils.assertSort(t2, "third operand", t0.sort.asInstanceOf[sorts.Seq].elementsSort)

    if (Verifier.config.useOldAxiomatization())
      createIfNonExistent(v0)
    else
      SeqAppend(SeqTake(t0,t1),SeqAppend(SeqSingleton(t2),SeqDrop(t0,Plus(t1,IntLiteral(1)))))
  }

  override def actualCreate(args: (Term, Term, Term)): SeqUpdate = new SeqUpdate(args._1, args._2, args._3)
}

/* Sets */

sealed trait SetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Set
}

sealed trait BinarySetOp extends SetTerm {
  val p0: Term
  val p1: Term
  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)
}

class EmptySet private[terms] (val elementsSort: Sort) extends ConditionalFlyweight[Sort, EmptySet] with SetTerm with Literal {
  val sort = sorts.Set(elementsSort)
  override lazy val toString = "Ø"
  override val equalityDefiningMembers: Sort = elementsSort
}

object EmptySet extends CondFlyweightTermFactory[Sort, EmptySet] {
  override def actualCreate(args: Sort): EmptySet = new EmptySet(args)
}

class SingletonSet private [terms] (val p: Term) extends ConditionalFlyweight[Term, SingletonSet] with SetTerm /* with UnaryOp[Term] */ {
  val elementsSort = p.sort
  val sort = sorts.Set(elementsSort)

  override lazy val toString = s"{$p}"
  override val equalityDefiningMembers: Term = p
}

object SingletonSet extends PreciseCondFlyweightFactory[Term, SingletonSet] {
  override def actualCreate(args: Term): SingletonSet = new SingletonSet(args)
}

class SetAdd private[terms] (val p0: Term, val p1: Term) extends SetTerm
    with ConditionalFlyweightBinaryOp[SetAdd] {

  val elementsSort = p0.sort.asInstanceOf[sorts.Set].elementsSort
  val sort = sorts.Set(elementsSort)

  override val op = "+"
}

object SetAdd extends CondFlyweightTermFactory[(Term, Term), SetAdd] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Set].elementsSort)

    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetAdd = new SetAdd(args._1, args._2)
}

class SetUnion(val p0: Term, val p1: Term) extends ConditionalFlyweightBinaryOp[SetUnion] with BinarySetOp {
  override val op = "∪"
}

object SetUnion extends PreciseCondFlyweightFactory[(Term, Term), SetUnion] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Set](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetUnion = new SetUnion(args._1, args._2)
}

class SetIntersection private[terms] (val p0: Term, val p1: Term) extends ConditionalFlyweightBinaryOp[SetIntersection] with BinarySetOp {
  override val op = "∩"
}

object SetIntersection extends PreciseCondFlyweightFactory[(Term, Term), SetIntersection] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Set](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetIntersection = new SetIntersection(args._1, args._2)
}

class SetSubset private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[SetSubset] {
  override val op = "⊂"
}

object SetSubset extends PreciseCondFlyweightFactory[(Term, Term), SetSubset] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Set](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetSubset = new SetSubset(args._1, args._2)
}

class SetDisjoint private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[SetDisjoint] {
  override val op = "disj"
}

object SetDisjoint extends PreciseCondFlyweightFactory[(Term, Term), SetDisjoint] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Set](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetDisjoint = new SetDisjoint(args._1, args._2)
}

class SetDifference private[terms] (val p0: Term, val p1: Term) extends ConditionalFlyweightBinaryOp[SetDifference] with BinarySetOp {
  override val op = "\\"
}

object SetDifference extends PreciseCondFlyweightFactory[(Term, Term), SetDifference] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Set](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetDifference = new SetDifference(args._1, args._2)
}

class SetIn private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[SetIn] {

  override val op = "in"
}

object SetIn extends PreciseCondFlyweightFactory[(Term, Term), SetIn] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t1, "second operand", "Set", _.isInstanceOf[sorts.Set])
    utils.assertSort(t0, "first operand", t1.sort.asInstanceOf[sorts.Set].elementsSort)

    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): SetIn = new SetIn(args._1, args._2)
}

class SetCardinality private[terms] (val p: Term) extends Term
    with ConditionalFlyweightUnaryOp[SetCardinality] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object SetCardinality extends PreciseCondFlyweightFactory[Term, SetCardinality] {
  override def apply(t: Term) = {
    utils.assertSort(t, "term", "Set", _.isInstanceOf[sorts.Set])
    createIfNonExistent(t)
  }

  override def actualCreate(args: Term): SetCardinality = new SetCardinality(args)
}

/* Multisets */

sealed trait MultisetTerm extends Term {
  val elementsSort: Sort
  val sort: sorts.Multiset
}

sealed trait BinaryMultisetOp extends MultisetTerm {

  val p0: Term
  val elementsSort = p0.sort.asInstanceOf[sorts.Multiset].elementsSort
  val sort = sorts.Multiset(elementsSort)
}

class EmptyMultiset private[terms] (val elementsSort: Sort) extends MultisetTerm with Literal with ConditionalFlyweight[Sort, EmptyMultiset] {
  val sort = sorts.Multiset(elementsSort)
  override lazy val toString = "Ø"
  override val equalityDefiningMembers: Sort = elementsSort
}

object EmptyMultiset extends PreciseCondFlyweightFactory[Sort, EmptyMultiset] {
  override def actualCreate(args: Sort): EmptyMultiset = new EmptyMultiset(args)
}

class SingletonMultiset private[terms] (val p: Term) extends MultisetTerm /* with UnaryOp[Term] */ with ConditionalFlyweight[Term, SingletonMultiset] {
  val elementsSort = p.sort
  val sort = sorts.Multiset(elementsSort)

  override lazy val toString = s"{$p}"
  override val equalityDefiningMembers: Term = p
}

object SingletonMultiset extends PreciseCondFlyweightFactory[Term, SingletonMultiset] {
  override def actualCreate(args: Term): SingletonMultiset = new SingletonMultiset((args))
}

class MultisetAdd private[terms] (val p0: Term, val p1: Term) extends BinaryMultisetOp
    with ConditionalFlyweightBinaryOp[MultisetAdd] {

  override val op = "+"
}

object MultisetAdd extends PreciseCondFlyweightFactory[(Term, Term), MultisetAdd] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Set", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Multiset].elementsSort)

    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetAdd = new MultisetAdd(args._1, args._2)
}

class MultisetUnion private[terms] (val p0: Term, val p1: Term) extends BinaryMultisetOp with ConditionalFlyweightBinaryOp[MultisetUnion] {
  override val op = "∪"
}

object MultisetUnion extends PreciseCondFlyweightFactory[(Term, Term), MultisetUnion] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetUnion = new MultisetUnion(args._1, args._2)
}

class MultisetIntersection private[terms] (val p0: Term, val p1: Term) extends BinaryMultisetOp with ConditionalFlyweightBinaryOp[MultisetIntersection] {
  override val op = "∩"
}

object MultisetIntersection extends PreciseCondFlyweightFactory[(Term, Term), MultisetIntersection] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetIntersection = new MultisetIntersection(args._1, args._2)
}

class MultisetSubset private[terms] (val p0: Term, val p1: Term) extends BooleanTerm
    with ConditionalFlyweightBinaryOp[MultisetSubset] {
  override val op = "⊂"
}

object MultisetSubset extends PreciseCondFlyweightFactory[(Term, Term), MultisetSubset] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetSubset = new MultisetSubset(args._1, args._2)
}

class MultisetDifference private[terms] (val p0: Term, val p1: Term) extends BinaryMultisetOp with ConditionalFlyweightBinaryOp[MultisetDifference] {
  override val op = "\\"
}

object MultisetDifference extends PreciseCondFlyweightFactory[(Term, Term), MultisetDifference] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSameSorts[sorts.Multiset](t0, t1)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetDifference = new MultisetDifference(args._1, args._2)
}

class MultisetCardinality private[terms] (val p: Term) extends Term
    with ConditionalFlyweightUnaryOp[MultisetCardinality] {

  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object MultisetCardinality extends PreciseCondFlyweightFactory[Term, MultisetCardinality] {
  override def apply(t: Term) = {
    utils.assertSort(t, "term", "Multiset", _.isInstanceOf[sorts.Multiset])
    createIfNonExistent(t)
  }

  override def actualCreate(args: Term): MultisetCardinality = new MultisetCardinality(args)
}

class MultisetCount private[terms] (val p0: Term, val p1: Term) extends Term
    with ConditionalFlyweightBinaryOp[MultisetCount] {

  val sort = sorts.Int
  override lazy val toString = s"$p0($p1)"
}

object MultisetCount extends PreciseCondFlyweightFactory[(Term, Term), MultisetCount] {
  override def apply(v0: (Term, Term)) = {
    val (ms, el) = v0
    utils.assertSort(ms, "first operand", "Multiset", _.isInstanceOf[sorts.Multiset])
    utils.assertSort(el, "second operand", ms.sort.asInstanceOf[sorts.Multiset].elementsSort)

    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MultisetCount = new MultisetCount(args._1, args._2)
}

/* Maps */

sealed trait MapTerm extends Term {
  val keySort: Sort
  val valueSort: Sort
  val sort: sorts.Map
}

class EmptyMap private[terms] (val keySort: Sort, val valueSort: Sort) extends MapTerm with Literal with ConditionalFlyweight[(Sort, Sort), EmptyMap] {
  val sort = sorts.Map(keySort, valueSort)
  override lazy val toString = "Ø"
  override val equalityDefiningMembers: (Sort, Sort) = (keySort, valueSort)
}

object EmptyMap extends PreciseCondFlyweightFactory[(Sort, Sort), EmptyMap] {
  override def actualCreate(args: (Sort, Sort)): EmptyMap = new EmptyMap(args._1, args._2)
}

class MapLookup private[terms] (val base: Term, val key: Term) extends Term with ConditionalFlyweightBinaryOp[MapLookup] {
  val sort: Sort = p0.sort.asInstanceOf[sorts.Map].valueSort
  override def p0: Term = base
  override def p1: Term = key
  override lazy val toString = s"$p0[$p1]"
}

object MapLookup extends PreciseCondFlyweightFactory[(Term, Term), MapLookup] {
  override def apply(v0: (Term, Term)) = {
    val (t0, t1) = v0
    utils.assertSort(t0, "first operand", "Map", _.isInstanceOf[sorts.Map])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Map].keySort)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term)): MapLookup = new MapLookup(args._1, args._2)
}

class MapCardinality private[terms] (val p: Term) extends Term with ConditionalFlyweightUnaryOp[MapCardinality] {
  val sort = sorts.Int
  override lazy val toString = s"|$p|"
}

object MapCardinality extends PreciseCondFlyweightFactory[Term, MapCardinality] {
  override def apply(t: Term) : MapCardinality = {
    utils.assertSort(t, "term", "Map", _.isInstanceOf[sorts.Map])
    createIfNonExistent(t)
  }

  override def actualCreate(args: Term): MapCardinality = new MapCardinality(args)
}

class MapUpdate private[terms] (val base: Term, val key: Term, val value: Term) extends MapTerm with ConditionalFlyweight[(Term, Term, Term), MapUpdate] {
  override val sort: sorts.Map = base.sort.asInstanceOf[sorts.Map]
  override val keySort: Sort = sort.keySort
  override val valueSort: Sort = sort.valueSort
  override val equalityDefiningMembers = (base, key, value)
}

object MapUpdate extends PreciseCondFlyweightFactory[(Term, Term, Term), MapUpdate] {
  override def apply(v0: (Term, Term, Term)) : MapUpdate = {
    val (t0, t1, t2) = v0
    utils.assertSort(t0, "first operand", "Map", _.isInstanceOf[sorts.Map])
    utils.assertSort(t1, "second operand", t0.sort.asInstanceOf[sorts.Map].keySort)
    utils.assertSort(t2, "third operand", t0.sort.asInstanceOf[sorts.Map].valueSort)
    createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Term, Term)): MapUpdate = new MapUpdate(args._1, args._2, args._3)
}

class MapDomain private[terms] (val p: Term) extends SetTerm with ConditionalFlyweightUnaryOp[MapDomain] {
  override val elementsSort: Sort = p.sort.asInstanceOf[sorts.Map].keySort
  override val sort: sorts.Set = sorts.Set(elementsSort)
  override lazy val toString = s"domain($p)"
}

object MapDomain extends PreciseCondFlyweightFactory[Term, MapDomain] {
  override def apply(t0: Term) = {
    utils.assertSort(t0, "term", "Map", _.isInstanceOf[sorts.Map])
    createIfNonExistent(t0)
  }

  override def actualCreate(args: Term): MapDomain = new MapDomain(args)
}

class MapRange private[terms] (val p: Term) extends SetTerm with ConditionalFlyweightUnaryOp[MapRange] {
  override val elementsSort: Sort = p.sort.asInstanceOf[sorts.Map].valueSort
  override val sort: sorts.Set = sorts.Set(elementsSort)
  override lazy val toString = s"range($p)"
}

object MapRange extends PreciseCondFlyweightFactory[Term, MapRange] {
  override def apply(t0: Term) = {
    utils.assertSort(t0, "term", "Map", _.isInstanceOf[sorts.Map])
    createIfNonExistent(t0)
  }

  override def actualCreate(args: Term): MapRange = new MapRange(args)
}

/* Snapshots */

sealed trait SnapshotTerm extends Term { val sort = sorts.Snap }

class Combine(val p0: Term, val p1: Term) extends SnapshotTerm
    with ConditionalFlyweightBinaryOp[Combine] {

  utils.assertSort(p0, "first operand", sorts.Snap)
  utils.assertSort(p1, "second operand", sorts.Snap)

  override lazy val toString = s"($p0, $p1)"
}

object Combine extends CondFlyweightTermFactory[(Term, Term), Combine] {
  override def apply(v0: (Term, Term)) = createIfNonExistent(v0._1.convert(sorts.Snap), v0._2.convert(sorts.Snap))

  override def actualCreate(args: (Term, Term)): Combine = new Combine(args._1, args._2)
}

class First(val p: Term) extends SnapshotTerm
    with ConditionalFlyweightUnaryOp[First]
    /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object First extends CondFlyweightTermFactory[Term, First] {
  override def apply(t: Term) = t match {
    case Combine(t1, _) => t1
    case _ => createIfNonExistent(t)
  }

  override def actualCreate(args: Term): First = new First(args)
}

class Second(val p: Term) extends SnapshotTerm
    with ConditionalFlyweightUnaryOp[Second]
    /*with PossibleTrigger*/ {

  utils.assertSort(p, "term", sorts.Snap)
}

object Second extends CondFlyweightTermFactory[Term, Second] {
  override def apply(t: Term) = t match {
    case Combine(_, t2) => t2
    case _ => createIfNonExistent(t)
  }

  override def actualCreate(args: Term): Second = new Second(args)
}

/* Quantified permissions */

class Lookup(val field: String, val fvf: Term, val at: Term) extends Term with ConditionalFlyweight[(String, Term, Term), Lookup] {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  override val equalityDefiningMembers: (String, Term, Term) = (field, fvf, at)
  val sort = fvf.sort.asInstanceOf[sorts.FieldValueFunction].codomainSort
}

object Lookup extends PreciseCondFlyweightFactory[(String, Term, Term), Lookup] {
  override def actualCreate(args: (String, Term, Term)): Lookup = new Lookup(args._1, args._2, args._3)
}

class PermLookup(val field: String, val pm: Term, val at: Term) extends Term with ConditionalFlyweight[(String, Term, Term), PermLookup] {
  utils.assertSort(pm, "field perm function", "FieldPermFunction", _.isInstanceOf[sorts.FieldPermFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  override val equalityDefiningMembers: (String, Term, Term) = (field, pm, at)
  val sort = sorts.Perm
}

object PermLookup extends PreciseCondFlyweightFactory[(String, Term, Term), PermLookup] {
  override def actualCreate(args: (String, Term, Term)): PermLookup = new PermLookup(args._1, args._2, args._3)
}

class Domain(val field: String, val fvf: Term) extends SetTerm /*with PossibleTrigger*/ with ConditionalFlyweight[(String, Term), Domain] {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])

  val elementsSort = sorts.Ref
  val sort = sorts.Set(elementsSort)
  override val equalityDefiningMembers: (String, Term) = (field, fvf)
}

object Domain extends CondFlyweightTermFactory[(String, Term), Domain] {
  override def actualCreate(args: (String, Term)): Domain = new Domain(args._1, args._2)
}

class FieldTrigger(val field: String, val fvf: Term, val at: Term) extends Term with ConditionalFlyweight[(String, Term, Term), FieldTrigger] {
  utils.assertSort(fvf, "field value function", "FieldValueFunction", _.isInstanceOf[sorts.FieldValueFunction])
  utils.assertSort(at, "receiver", sorts.Ref)

  val sort = sorts.Bool
  override val equalityDefiningMembers: (String, Term, Term) = (field, fvf, at)
}

object FieldTrigger extends PreciseCondFlyweightFactory[(String, Term, Term), FieldTrigger] {
  override def actualCreate(args: (String, Term, Term)): FieldTrigger = new FieldTrigger(args._1, args._2, args._3)
}

/* Quantified predicates */

class PredicateLookup(val predname: String, val psf: Term, val args: Seq[Term]) extends Term with ConditionalFlyweight[(String, Term, Seq[Term]), PredicateLookup] {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])

  val sort = psf.sort.asInstanceOf[sorts.PredicateSnapFunction].codomainSort
  override val equalityDefiningMembers: (String, Term, Seq[Term]) = (predname, psf, args)
}

object PredicateLookup extends PreciseCondFlyweightFactory[(String, Term, Seq[Term]), PredicateLookup] {
  override def actualCreate(args: (String, Term, Seq[Term])): PredicateLookup = new PredicateLookup(args._1, args._2, args._3)
}

class PredicatePermLookup(val predname: String, val pm: Term, val args: Seq[Term]) extends Term with ConditionalFlyweight[(String, Term, Seq[Term]), PredicatePermLookup] {
  utils.assertSort(pm, "predicate perm function", "PredicatePermFunction", _.isInstanceOf[sorts.PredicatePermFunction])

  val sort = sorts.Perm
  override val equalityDefiningMembers: (String, Term, Seq[Term]) = (predname, pm, args)
}

object PredicatePermLookup extends PreciseCondFlyweightFactory[(String, Term, Seq[Term]), PredicatePermLookup] {
  override def actualCreate(args: (String, Term, Seq[Term])): PredicatePermLookup = new PredicatePermLookup(args._1, args._2, args._3)
}

class PredicateDomain(val predname: String, val psf: Term) extends SetTerm /*with PossibleTrigger*/ with ConditionalFlyweight[(String, Term), PredicateDomain] {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])
  val elementsSort = sorts.Snap
  val sort = sorts.Set(elementsSort)
  override val equalityDefiningMembers: (String, Term) = (predname, psf)
}

object PredicateDomain extends CondFlyweightTermFactory[(String, Term), PredicateDomain] {
  override def actualCreate(args: (String, Term)): PredicateDomain = new PredicateDomain(args._1, args._2)
}

class PredicateTrigger(val predname: String, val psf: Term, val args: Seq[Term]) extends Term with ConditionalFlyweight[(String, Term, Seq[Term]), PredicateTrigger] {
  utils.assertSort(psf, "predicate snap function", "PredicateSnapFunction", _.isInstanceOf[sorts.PredicateSnapFunction])

  val sort = sorts.Bool
  override val equalityDefiningMembers: (String, Term, Stack[Term]) = (predname, psf, args)
}

object PredicateTrigger extends PreciseCondFlyweightFactory[(String, Term, Seq[Term]), PredicateTrigger] {
  override def actualCreate(args: (String, Term, Seq[Term])): PredicateTrigger = new PredicateTrigger(args._1, args._2, args._3)
}

/* Magic wands */

/**
 * Represents a snapshot of a magic wand, which is a function from `Snap` to `Snap`.
 *
 * @param mwsf The function that represents the snapshot of the magic wand. It is a variable of sort [[sorts.MagicWandSnapFunction]].
 *             In the symbolic execution when we apply a magic wand, it consumes the left-hand side
 *             and uses this function and the resulting snapshot to look up which right-hand side to produce.
 */
class MagicWandSnapshot(val mwsf: Term) extends Term with ConditionalFlyweight[Term, MagicWandSnapshot] {
  utils.assertSort(mwsf, "magic wand snap function", sorts.MagicWandSnapFunction)

  override val sort: Sort = sorts.MagicWandSnapFunction

  override lazy val toString = s"wandSnap($mwsf)"

  override val equalityDefiningMembers: Term = mwsf

  /**
   * Apply the given snapshot of the left-hand side to the magic wand map to get the snapshot of the right-hand side
   * which includes the values of the left-hand side.
   *
   * @param snapLhs The snapshot of the left-hand side that should be applied to the magic wand map.
   * @return The snapshot of the right-hand side that preserves the values of the left-hand side.
   */
  def applyToMWSF(snapLhs: Term): Term = MWSFLookup(mwsf, snapLhs)
}

object MagicWandSnapshot extends PreciseCondFlyweightFactory[Term, MagicWandSnapshot]  {
  /** Create an instance of [[viper.silicon.state.terms.MagicWandSnapshot]]. */
  override def actualCreate(arg: Term): MagicWandSnapshot =
    new MagicWandSnapshot(arg)
}

/**
 * Term that applies a [[sorts.MagicWandSnapFunction]] to a snapshot.
 * It returns a snapshot for the RHS of a magic wand that includes that values of the given snapshot.
 *
 * @param mwsf Term of sort [[sorts.MagicWandSnapFunction]]. Function from `Snap` to `Snap`.
 * @param snap Term of sort [[sorts.Snap]] to which the MWSF is applied to. It represents the values of the wand's LHS.
 */
class MWSFLookup(val mwsf: Term, val snap: Term) extends Term with ConditionalFlyweightBinaryOp[MWSFLookup] {
  val sort: Sort = sorts.Snap
  override def p0: Term = mwsf
  override def p1: Term = snap
  override lazy val toString = s"$mwsf[$snap]"
}

object MWSFLookup extends PreciseCondFlyweightFactory[(Term, Term), MWSFLookup] {
  override def apply(pair: (Term, Term)): MWSFLookup = {
    val (mwsf, snap) = pair
    utils.assertSort(mwsf, "mwsf", sorts.MagicWandSnapFunction)
    utils.assertSort(snap, "snap", sorts.Snap)
    createIfNonExistent(pair)
  }

  /** Create an instance of [[viper.silicon.state.terms.MWSFLookup]]. */
  override def actualCreate(args: (Term, Term)): MWSFLookup =
    new MWSFLookup(args._1, args._2)
}

class MagicWandChunkTerm(val chunk: MagicWandChunk) extends Term with ConditionalFlyweight[MagicWandChunk, MagicWandChunkTerm] {
  override val sort = sorts.Unit /* TODO: Does this make sense? */
  override lazy val toString = s"wand@${chunk.id.ghostFreeWand.pos}}"
  override val equalityDefiningMembers: MagicWandChunk = chunk
}

object MagicWandChunkTerm extends CondFlyweightTermFactory[MagicWandChunk, MagicWandChunkTerm] {
  override def actualCreate(args: MagicWandChunk): MagicWandChunkTerm = new MagicWandChunkTerm(args)
}

/* Factory methods for all resources */

object toSnapTree extends (Seq[Term] => Term) {
  private def binaryCombine(t0: Term, t1: Term) = Combine(t0, t1)
  @inline
  def apply(args: Seq[Term]): Term = {
    if (args.isEmpty) Unit
    else args.map(_.convert(sorts.Snap)).reduceLeft(binaryCombine)
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
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term], program: ast.Program): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args, program)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): FieldTrigger =
    FieldTrigger(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicateTrigger =
    PredicateTrigger(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term], program: ast.Program): PredicateTrigger = {
    val wandId = MagicWandIdentifier(wand, program).toString

    PredicateTrigger(wandId, sm, args)
  }
}

object ResourceLookup {
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term], program: ast.Program): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args, program)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): Lookup =
    Lookup(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicateLookup =
    PredicateLookup(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term], program: ast.Program): PredicateLookup = {
    val wandId = MagicWandIdentifier(wand, program).toString

    PredicateLookup(wandId, sm, args)
  }
}

object ResourcePermissionLookup {
  def apply(resource: ast.Resource, sm: Term, args: Seq[Term], program: ast.Program): Term = {
    resource match {
      case f: ast.Field =>
        assert(args.size == 1)
        apply(f, sm, args.head)
      case p: ast.Predicate => apply(p, sm, args)
      case w: ast.MagicWand => apply(w, sm, args, program)
    }
  }

  def apply(field: ast.Field, sm: Term, rcvr: Term): PermLookup =
    PermLookup(field.name, sm, rcvr)

  def apply(predicate: ast.Predicate, sm: Term, args: Seq[Term]): PredicatePermLookup =
    PredicatePermLookup(predicate.name, sm, args)

  def apply(wand: ast.MagicWand, sm: Term, args: Seq[Term], program: ast.Program): PredicatePermLookup = {
    val wandId = MagicWandIdentifier(wand, program).toString

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
 * because they are optimised away if wrapped `t` already has sort `to`.
 */
class SortWrapper(val t: Term, val to: Sort)
    extends Term
       with ConditionalFlyweight[(Term, Sort), SortWrapper] {

  assert((t.sort == sorts.Snap || to == sorts.Snap) && t.sort != to,
         s"Unexpected sort wrapping of $t from ${t.sort} to $to")

  val equalityDefiningMembers = (t, to)
//  override lazy val toString = s"SortWrapper($t, $to)"
  override lazy val toString = t.toString
  override val sort = to
}

object SortWrapper extends CondFlyweightTermFactory[(Term, Sort), SortWrapper] {
  override def apply(v0: (Term, Sort)) = v0 match {
    case (t, to) if t.sort == to => t
    case (sw: SortWrapper, to) if sw.t.sort == to => sw.t
    case _ => createIfNonExistent(v0)
  }

  override def actualCreate(args: (Term, Sort)): SortWrapper = new SortWrapper(args._1, args._2)
}

/* Other terms */

class Distinct(val ts: Set[DomainFun]) extends BooleanTerm with ConditionalFlyweight[Set[DomainFun], Distinct] {
  assert(ts.size >= 2, "Distinct requires at least two terms")

  val equalityDefiningMembers = ts
  override lazy val toString = s"Distinct($ts)"
}

object Distinct extends CondFlyweightTermFactory[Set[DomainFun], Distinct] {
  override def apply(ts: Set[DomainFun]): Term =
    if (ts.size >= 2) createIfNonExistent(ts)
    else True

  override def actualCreate(args: Set[DomainFun]): Distinct = new Distinct(args)
}

class Let(val bindings: Map[Var, Term], val body: Term) extends Term with ConditionalFlyweight[(Map[Var, Term], Term), Let] {
  assert(bindings.nonEmpty, "Let needs to bind at least one variable")

  val sort = body.sort
  val equalityDefiningMembers = (bindings, body)

  override lazy val toString = s"let ${bindings.map(p => s"${p._1} = ${p._2}")} in $body"
}

object Let extends CondFlyweightTermFactory[(Map[Var, Term], Term), Let] {
  def apply(v: Var, t: Term, body: Term): Term = apply(Map(v -> t), body)
  def apply(vs: Seq[Var], ts: Seq[Term], body: Term): Term = apply(toMap(vs zip ts), body)

  override def apply(v0: (Map[Var, Term], Term)): Term = {
    val (bindings, body) = v0
    if (bindings.isEmpty) body
    else createIfNonExistent(v0)
  }

  override def actualCreate(args: (Map[Var, Term], Term)): Let = new Let(args._1, args._2)
}

/* Predefined terms */

object predef {
  val `?s` = Var(Identifier("s@$"), sorts.Snap, false) // with SnapshotTerm
  val `?r` = Var(Identifier("r"), sorts.Ref, false)

  val Zero = IntLiteral(0)
  val One = IntLiteral(1)
}

/* Convenience functions */

object perms {
  def IsNonNegative(p: Term): Term =
    Or(p === NoPerm, IsPositive(p))
      /* All basic static simplifications should be covered by Equals,
       * IsPositive and or
       */

  def IsNonNegative(e: ast.Exp)(pos: ast.Position = ast.NoPosition, info: ast.Info = ast.NoInfo, errT: ast.ErrorTrafo = ast.NoTrafos): ast.Exp =
    ast.GeCmp(e, ast.NoPerm()())(pos, info, errT)

  def IsPositive(p: Term): Term = p match {
    case p: PermLiteral => if (p.literal > Rational.zero) True else False
    case _ => PermLess(NoPerm, p)
  }

  def IsPositive(e: ast.Exp)(pos: ast.Position = ast.NoPosition, info: ast.Info = ast.NoInfo, errT: ast.ErrorTrafo = ast.NoTrafos): ast.Exp =
    ast.GtCmp(e, ast.NoPerm()())(pos, info, errT)

  def IsNonPositive(p: Term): Term = p match {
    case p: PermLiteral => if (p.literal <= Rational.zero) True else False
    case _ => Or(p === NoPerm, PermLess(p, NoPerm))
  }

  def IsNonPositive(e: ast.Exp)(pos: ast.Position = ast.NoPosition, info: ast.Info = ast.NoInfo, errT: ast.ErrorTrafo = ast.NoTrafos): ast.Exp =
    ast.LeCmp(e, ast.NoPerm()())(pos, info, errT)

  def BigPermSum(it: Iterable[Term], f: Term => Term = t => t): Term = {
    def binaryPermPlus(t0: Term, t1: Term) = PermPlus(t0, t1)
    viper.silicon.utils.mapReduceLeft(it, f, binaryPermPlus, NoPerm)
  }
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
    case Ite(_, t0, NoPerm) => consumeExactRead(t0, constrainableARPs)
    case Ite(_, NoPerm, t1) => consumeExactRead(t1, constrainableARPs)
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
