// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.silicon.extensions

import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse

/** An AST rewriter that transforms accessibility predicates under conditionals into accessibility
  * predicates with corresponding conditional permission expressions. E.g. it transforms
  *   b ==> acc(x.f, p)
  * to
  *   acc(x.f, b ? p : none)
  *
  * TODO: Support magic wands
  * TODO: Support ternary expressions b ? a1 : a2
  */
class ConditionalPermissionRewriter {
  private val rewriter = ViperStrategy.Context[Condition]({
    // TODO: Support ternary expressions b ? a1 : a2
    //
    // General note regarding the AST transformer framework: the new node, i.e. the node returned in
    // a match case, will not itself be visited again. The recurseFunc, defined below, will determine
    // which of the new node's children will be visited.
    case (Implies(cond, acc: AccessPredicate), cc) =>
      // Found an implication b ==> acc(...)
      (conditionalize(acc, cc.c &*& cond), cc) // Won't recurse into acc's children (see recurseFunc below)

    case (impl: Implies, cc) if !impl.right.isPure =>
      // Entering an implication b ==> A, where A is not pure, i.e. contains an accessibility accessibility
      (impl.right, cc.updateContext(cc.c &*& impl.left))

    case (acc: AccessPredicate, cc) if cc.c.optExp.nonEmpty =>
      // Found an accessibility predicate nested under some conditionals
      (conditionalize(acc, cc.c), cc) // Won't recurse into acc's children

    case (exp: Exp, cc) if cc.c.optExp.nonEmpty && exp.isPure =>
      // Found a pure expression nested under some conditionals
      val cond = cc.c.exp
      (Implies(cond, exp)(cond.pos, cond.info, cond.errT), cc) // Won't recurse into exp's children
  }, Condition(), Traverse.TopDown).recurseFunc({
    case exp: Exp if exp.isPure => Nil // Don't recurse into pure expressions
    case _: AccessPredicate => Nil // Don't recurse into accessibility predicates
  })

  /** Transforms all conditional accessibility predicates in `root` into unconditional accessibility
    * predicates with suitable conditional permission expressions.
    */
  def rewrite(root: Node): Node = {
    rewriter.execute(root)
  }

  /** Convenient factory for a node CondExp(cond, perm). */
  private def makeCondExp(cond: Exp, perm: Exp): CondExp = {
    CondExp(cond, perm, NoPerm()(perm.pos, perm.info, perm.errT))(perm.pos, perm.info, perm.errT)
  }

  /** Makes `acc`'s permissions conditional w.r.t. `cond`.
    * TODO: Support magic wands
    */
  private def conditionalize(acc: AccessPredicate, cond: Condition): AccessPredicate = {
    acc match {
      case FieldAccessPredicate(loc, perm) =>
        FieldAccessPredicate(loc, makeCondExp(cond.exp, perm))(acc.pos, acc.info, acc.errT)
      case PredicateAccessPredicate(loc, perm) =>
        PredicateAccessPredicate(loc, makeCondExp(cond.exp, perm))(acc.pos, acc.info, acc.errT)
      case wand: MagicWand =>
        sys.error(s"Cannot conditionalise magic wand $wand (${viper.silicon.utils.ast.sourceLineColumn(wand)})")
    }
  }
}

/** Class Condition represents a potentially vacuous (i.e. true) condition that can be strengthened
  * by adding another conjunct.
  *
  * @param optExp Optional condition, with `None` representing the vacuous condition `true`.
  */
private final case class Condition(optExp: Option[Exp] = None) {
  /** Returns a new condition that represents the conjunction of this and the other expression.
    * If `this.optExp` is `None`, the returned condition will just be the other. E.g. `b1 &*& b2`
    * will yield `b1 && b2`, whereas `None &*& b2` will yields just `b2`.
    *
    * @param other The additional conjunct.
    * @return The logical conjunction of this and the other conjunct.
    */
  def &*&(other: Exp): Condition = {
    val newExp = optExp match {
      case None => other
      case Some(exp) => And(exp, other)(other.pos, other.info, other.errT)
    }

    Condition(Some(newExp))
  }

  def exp: Exp = optExp.getOrElse(TrueLit()())
}
