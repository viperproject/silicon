/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package state.terms

import silver.ast.utility.GenericTriggerGenerator

import scala.Predef.Map

object TriggerGenerator extends GenericTriggerGenerator[Term, Sort, Term, Var, Quantification, PossibleTrigger,
                                                        ForbiddenInTrigger, Nothing, Nothing, Trigger] {

  protected def hasSubnode(root: Term, child: Term) = root.hasSubterm(child)
  protected def visit[A](root: Term)(f: PartialFunction[Term, A]) = root.visit(f)
  protected def deepCollect[A](root: Term)(f: PartialFunction[Term, A]) = root.deepCollect(f)
  protected def reduceTree[A](root: Term)(f: (Term, Seq[A]) => A) = root.reduceTree(f)
  protected def transform[T <: Term](root: T)(f: PartialFunction[Term, Term]) = root.transform(f)()
  protected def quantifiedVariables(q: Quantification) = q.vars
  protected def exps(trigger: Trigger) = trigger.p

  /* Attention: Don't accidentially make def Trigger/Var recursive by omitting
   * the prefix to state.terms.Trigger/Var!
   */
  protected def Trigger(terms: Seq[Term]) = state.terms.Trigger(terms)
  protected def Var(id: String, sort: Sort) = state.terms.Var(id, sort)

  protected val wrapperMap: Map[Class[_], PossibleTrigger => Nothing] = Map.empty
}
