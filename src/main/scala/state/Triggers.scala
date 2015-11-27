/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state.terms

import viper.silver.ast.utility.{GenericArithmeticSolver, GenericTriggerGenerator, GenericAxiomRewriter}
import reporting.MultiRunLogger
import silicon.utils.Counter

class Trigger private[terms] (val p: Seq[Term]) extends StructuralEqualityUnaryOp[Seq[Term]] {
  override val toString = s"{${p.mkString(",")}}"
}

object Trigger extends (Seq[Term] => Trigger) {
  def apply(t: Term) = new Trigger(t :: Nil)
  def apply(ts: Seq[Term]) = new Trigger(ts)

  def unapply(trigger: Trigger) = Some(trigger.p)
}

object TriggerGenerator extends GenericTriggerGenerator[Term, Sort, Term, Var, Quantification, PossibleTrigger,
                                                        Nothing, Nothing] {

  protected def hasSubnode(root: Term, child: Term) = root.hasSubterm(child)
  protected def visit[A](root: Term)(f: PartialFunction[Term, A]) = root.visit(f)
  protected def deepCollect[A](root: Term)(f: PartialFunction[Term, A]) = root.deepCollect(f)
  protected def reduceTree[A](root: Term)(f: (Term, Seq[A]) => A) = root.reduceTree(f)
  protected def transform[T <: Term](root: T)(f: PartialFunction[Term, Term]) = root.transform(f)()
  protected def Quantification_vars(q: Quantification) = q.vars
  protected def Exp_typ(term: Term): Sort = term.sort
  protected def Var(id: String, sort: Sort) = state.terms.Var(id, sort)
  protected val wrapperMap: Predef.Map[Class[_], PossibleTrigger => Nothing] = Predef.Map.empty

  def generateFirstTriggerGroup(vs: Seq[Var], toSearch: Seq[Term]): Option[(Seq[Trigger], Seq[Var])] =
    generateFirstTriggerSetGroup(vs, toSearch).map {
      case (triggerSet, extraVars) => (triggerSet.map(set => Trigger(set.exps)), extraVars)
    }

  /* Note: If Plus and Minus were type arguments of GenericTriggerGenerator, the latter
   *       could implement isForbiddenInTrigger already */
  protected def isForbiddenInTrigger(term: Term) = term match {
    case _: Plus | _: Minus if allowInvalidTriggers => false
    case _: ForbiddenInTrigger => true
    case _ => false
  }
}

class AxiomRewriter(counter: Counter, logger: MultiRunLogger)
    extends GenericAxiomRewriter[Sort, Term, Var, Quantification, Equals, And, Implies, Plus, Minus,
                                 Trigger, ForbiddenInTrigger] {

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

  protected def Eq(e1: Exp, e2: Exp) = state.terms.Equals(e1, e2)
  protected def And(es: Seq[Exp]) = state.terms.And(es)
  protected def Implies(e1: Exp, e2: Exp) = state.terms.Implies(e1, e2)

  protected def Var_id(v: Var) = v.id

  protected def Quantification_triggers(q: Quantification) = q.triggers
  protected def Quantification_vars(q: Quantification) = q.vars
  protected def Quantification_body(q: Quantification) = q.body

  protected def Quantification_copy(q: Quantification, vars: Seq[Var], body: Exp, triggers: Seq[Trigger]) =
    q.copy(vars = vars, body = body, triggers = triggers)

  protected def Trigger_exps(t: Trigger) = t.p
  protected def Trigger(exps: Seq[Exp]) = state.terms.Trigger(exps)

  /*
   * Abstract members - dependencies
   */

  protected val solver = SimpleArithmeticSolver

  protected def fresh(name: String, typ: Type) = Var(s"$name@rw${counter.next()}", typ)

  protected def log(message: String): Unit = {
    logger.println(message)
  }

  protected def log(key: String, item: Any) {
    log(key, item :: Nil)
  }

  protected def log(key: String, items: Iterable[Any]) {
    if (items.size <= 1)
      logger.println(s"  $key: $items")
    else {
      logger.println(s"  $key:")
      items foreach (item => logger.println(s"    $item"))
    }
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

  protected def Plus_apply(e1: Exp, e2: Exp) = state.terms.Plus(e1, e2)
  protected def Plus_unapply(plus: Plus) = (plus.p0, plus.p1)

  protected def Minus_apply(e1: Exp, e2: Exp) = state.terms.Minus(e1, e2)
  protected def Minus_unapply(minus: Minus) = (minus.p0, minus.p1)
}
