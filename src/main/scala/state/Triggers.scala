/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.state.terms

import viper.silver.ast.utility.{GenericArithmeticSolver, GenericTriggerGenerator, GenericAxiomRewriter}
import viper.silicon.utils.Counter
import viper.silicon.state.{Identifier, terms}

class Trigger private[terms] (val p: Seq[Term]) extends StructuralEqualityUnaryOp[Seq[Term]] {
  override val toString = s"{${p.mkString(",")}}"
}

object Trigger extends (Seq[Term] => Trigger) {
  def apply(t: Term) = new Trigger(t :: Nil)
  def apply(ts: Seq[Term]) = new Trigger(ts)

  def unapply(trigger: Trigger) = Some(trigger.p)
}

/** Attention: The trigger generator is *not* thread-safe, among other things because its
  * filters for accepting/rejecting possible triggers can be changed
  * (see, e.g. [[GenericTriggerGenerator.setCustomIsForbiddenInTrigger]]).
  */
class TriggerGenerator
    extends GenericTriggerGenerator[Term, Sort, Term, Var, Quantification]
       with Mutable {

  protected def hasSubnode(root: Term, child: Term) = root.hasSubterm(child)
  protected def visit[A](root: Term)(f: PartialFunction[Term, A]) = root.visit(f)
  protected def deepCollect[A](root: Term)(f: PartialFunction[Term, A]) = root.deepCollect(f)
  protected def reduceTree[A](root: Term)(f: (Term, Seq[A]) => A) = root.reduceTree(f)
  protected def transform[T <: Term](root: T)(f: PartialFunction[Term, Term]) = root.transform(f)()
  protected def Quantification_vars(q: Quantification) = q.vars
  protected def Exp_typ(term: Term): Sort = term.sort
  protected def Var(id: String, sort: Sort) = terms.Var(Identifier(id), sort)

  def generateFirstTriggerGroup(vs: Seq[Var], toSearch: Seq[Term]): Option[(Seq[Trigger], Seq[Var])] =
    generateFirstTriggerSetGroup(vs, toSearch).map {
      case (triggerSet, extraVars) => (triggerSet.map(set => Trigger(set.exps)), extraVars)
    }

  def assembleQuantification(quantifier: Quantifier,
                             qvars: Seq[Var],
                             body: Term,
                             toSearch: Seq[Term],
                             qid: String,
                             isGlobal: Boolean,
                             axiomRewriter: AxiomRewriter)
                            : Quantification = {

    setCustomIsForbiddenInTrigger(advancedIsForbiddenInTrigger)

    val (triggers, extraVars) = generateFirstTriggerGroup(qvars, toSearch).getOrElse((Nil, Nil))

    setCustomIsForbiddenInTrigger(PartialFunction.empty)

    val quantification = Quantification(quantifier, qvars ++ extraVars, body, triggers, qid, isGlobal)
    val finalQuantification = axiomRewriter.rewrite(quantification).getOrElse(quantification)

    finalQuantification
  }

  def assembleQuantification(quantifier: Quantifier,
                             qvars: Seq[Var],
                             body: Term,
                             triggers: Seq[Trigger],
                             qid: String,
                             isGlobal: Boolean,
                             axiomRewriter: AxiomRewriter)
                            (implicit dummyImplicit: DummyImplicit)
                            : Quantification = {

    val quantification = Quantification(quantifier, qvars, body, triggers, qid, isGlobal)
    val finalQuantification = axiomRewriter.rewrite(quantification).getOrElse(quantification)

    finalQuantification
  }

  /* True iff the given node is a possible trigger */
  def isPossibleTrigger(e: Term): Boolean = e match {
    case _: Var => false
    case app: App => app.applicable.isInstanceOf[Function]
    case   _: CustomEquals
         | _: PermMin
         | _: SeqTerm
         | _: SeqLength
         | _: SeqAt
         | _: SeqIn
         | _: SetTerm
         | _: SetIn
         | _: SetCardinality
         | _: MultisetTerm
         | _: MultisetCardinality
         | _: MultisetCount
         | _: SnapshotTerm
         | _: Domain
         | _: Lookup
         | _: PredicateLookup
         => true
    case _ => false
  }

  /* True iff the given node is not allowed in triggers */
  def isForbiddenInTrigger(term: Term) = term match {
    case app: App => app.applicable.isInstanceOf[Macro]
    case   _: Plus | _: Minus | _: Times | _: Div | _: Mod
         | _: Not | _: Or | _: And | _: Implies | _: Iff | _: Ite
         | _: BuiltinEquals
         | _: Less | _: AtMost | _: Greater | _: AtLeast
         | _: PermTimes | _: IntPermTimes | _: PermIntDiv | _: PermPlus | _: PermMinus
         | _: PermLess | _: PermAtMost
         | _: Distinct
         | _: Let
         => true
    case _ => false
  }

  val advancedIsForbiddenInTrigger:PartialFunction[Term, Boolean] = {
    case _: Plus | _: Minus => false
  }

  protected def withArgs(term: Term, args: Seq[Term]): Term = {
    val subterms = term.subterms

    assert(subterms.length == args.length,
             s"Cannot create a new instance of ${term.getClass.getSimpleName} with arguments $args: "
           + s"${term.getClass.getSimpleName} only requires ${subterms.length} subterms, but "
           + s"${args.length} arguments were provided")

    subterms.zip(args).foldLeft(term) { case (t, (sub, arg)) =>
      if (sub == arg) t
      else t.replace(sub, arg)
    }
  }

  protected def getArgs(term: Term): Seq[Term] = term.subterms
}

class AxiomRewriter(counter: Counter/*, logger: MultiRunLogger*/,
                    triggerGenerator: GenericTriggerGenerator[Term, Sort, Term, Var, Quantification])
    extends GenericAxiomRewriter[Sort, Term, Var, Quantification, Equals, And, Implies, Plus, Minus,
                                 Trigger] {

  /*
   * Local members (not required by GenericAxiomRewriter)
   */

  private type Type = Sort
  private type Exp = Term
  private type Eq = Equals

  def rewrite(quantification: Quantification): Option[Quantification] =
    rewrite(quantification, quantification.triggers.map(trigger => TriggerSet(trigger.p)))

  /*
   * Abstract members - type arguments
   */

  protected def Exp_type(exp: Exp) = exp.sort
  protected def Exp_shallowCollect[R](node: Exp)(f: PartialFunction[Exp, R]) = node.shallowCollect(f)
  protected def Exp_contains(node: Exp, other: Exp) = node.contains(other)
  protected def Exp_replace(node: Exp, original: Exp, replacement: Exp) = node.replace(original, replacement)

  protected def Eq(e1: Exp, e2: Exp) = terms.Equals(e1, e2)
  protected def And(es: Seq[Exp]) = terms.And(es)
  protected def Implies(e1: Exp, e2: Exp) = terms.Implies(e1, e2)

  protected def Var_id(v: Var) = v.id.name

  protected def Quantification_triggers(q: Quantification) = q.triggers
  protected def Quantification_vars(q: Quantification) = q.vars
  protected def Quantification_body(q: Quantification) = q.body

  protected def Quantification_copy(q: Quantification, vars: Seq[Var], body: Exp, triggers: Seq[Trigger]) =
    q.copy(vars = vars, body = body, triggers = triggers)

  protected def Trigger_exps(t: Trigger) = t.p
  protected def Trigger(exps: Seq[Exp]) = terms.Trigger(exps)

  /* True iff the given node is not allowed in triggers */
  protected def isForbiddenInTrigger(e: Exp): Boolean = triggerGenerator.isForbiddenInTrigger(e)

  /*
   * Abstract members - dependencies
   */

  protected val solver = SimpleArithmeticSolver

  protected def fresh(name: String, typ: Type): Var =
    Var(Identifier(s"$name@rw${counter.next()}"), typ)

  protected def log(message: String): Unit = {
//    logger.println(message)
  }

  protected def log(key: String, item: Any) {
    log(key, item :: Nil)
  }

  protected def log(key: String, items: Iterable[Any]) {
//    if (items.size <= 1)
//      logger.println(s"  $key: $items")
//    else {
//      logger.println(s"  $key:")
//      items foreach (item => logger.println(s"    $item"))
//    }
  }
}

object SimpleArithmeticSolver extends GenericArithmeticSolver[Sort, Term, Var, Plus, Minus] {

  /*
   * Local members (not required by GenericAxiomRewriter)
   */

  private type Type = Sort
  private type Exp = Term
  private type Eq = Equals

  /*
   * Abstract members - type arguments
   */

  protected def Exp_type(exp: Exp) = exp.sort
  protected def Exp_deepCollect[A](node: Exp)(f: PartialFunction[Exp, A]) = node.deepCollect(f)
  protected def Exp_contains(node: Exp, other: Exp) = node.contains(other)

  protected def Type_isInt(typ: Type) = typ == sorts.Int

  protected def Plus_apply(e1: Exp, e2: Exp) = terms.Plus(e1, e2)
  protected def Plus_unapply(plus: Plus) = (plus.p0, plus.p1)

  protected def Minus_apply(e1: Exp, e2: Exp) = terms.Minus(e1, e2)
  protected def Minus_unapply(minus: Minus) = (minus.p0, minus.p1)
}
