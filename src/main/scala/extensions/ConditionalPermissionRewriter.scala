// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.silicon.extensions

import viper.silver.ast._
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.ast.utility.rewriter.Traverse

import scala.collection.mutable

/** An AST rewriter that transforms accessibility predicates under conditionals into accessibility
  * predicates with corresponding conditional permission expressions. E.g. it transforms
  *   b ==> acc(x.f, p)
  * to
  *   acc(x.f, b ? p : none)
  *
  */
class ConditionalPermissionRewriter {
  private def rewriter(implicit p: Program, allowCondWildcard: Boolean, alreadySeen: mutable.HashSet[Exp]) = ViperStrategy.Context[Condition]({
    // Does NOT rewrite ternary expressions; those have to be transformed to implications in advance
    // using the ternaryRewriter below.
    //
    // General note regarding the AST transformer framework: the new node, i.e. the node returned in
    // a match case, will not itself be visited again. The recurseFunc, defined below, will determine
    // which of the new node's children will be visited.
    case (i@Implies(cond, acc: AccessPredicate), cc) =>
      // Found an implication b ==> acc(...)
      // Transformation causes issues if the permission involve a wildcard, so we avoid that case.
      // Also, we cannot push perm and forperm expressions further in, since their value may be different at different
      // places in the same assertion.
      val res = if ((allowCondWildcard || !acc.perm.contains[WildcardPerm]) && !Expressions.containsPermissionIntrospection(cond))
        (conditionalize(acc, cc.c &*& cond, allowCondWildcard), cc) // Won't recurse into acc's children (see recurseFunc below)
      else
        (Implies(And(cc.c.exp, cond)(), acc)(i.pos, i.info, i.errT), cc)
      alreadySeen.add(res._1)
      res

    case (i@Implies(cond, l: Let), cc) if !l.isPure =>
      if (Expressions.proofObligations(l.exp)(p).isEmpty && !Expressions.containsPermissionIntrospection(cond)) {
        (l, cc.updateContext(cc.c &*& cond))
      } else {
        // bound expression might only be well-defined under context condition;
        // thus, don't push conditions further in.
        val res = (Implies(And(cc.c.exp, cond)(), l)(i.pos, i.info, i.errT), cc)
        alreadySeen.add(res._1)
        res
      }

    case (impl: Implies, cc) if !impl.right.isPure =>
      // Entering an implication b ==> A, where A is not pure, i.e. contains an accessibility accessibility
      if (Expressions.containsPermissionIntrospection(impl.left)) {
        (Implies(And(cc.c.exp, impl.left)(), impl.right)(impl.pos, impl.info, impl.errT), cc)
      } else {
        (impl.right, cc.updateContext(cc.c &*& impl.left))
      }

    case (acc: AccessPredicate, cc) if cc.c.optExp.nonEmpty =>
      // Found an accessibility predicate nested under some conditionals
      // Wildcards may cause issues, see above.
      val res = if (allowCondWildcard || !acc.perm.contains[WildcardPerm])
        (conditionalize(acc, cc.c, allowCondWildcard), cc) // Won't recurse into acc's children
      else
        (Implies(cc.c.exp, acc)(acc.pos, acc.info, acc.errT), cc)
      alreadySeen.add(res._1)
      res

    case (l: Let, cc) if Expressions.proofObligations(l.exp)(p).nonEmpty =>
      // Bound expression might only be well-defined under context conditions;
      // thus, don't push conditions further in.
      val res = (Implies(cc.c.exp, l)(l.pos, l.info, l.errT), cc)
      alreadySeen.add(res._1)
      res

    case (exp: Exp, cc) if cc.c.optExp.nonEmpty && exp.isPure =>
      // Found a pure expression nested under some conditionals
      val cond = cc.c.exp
      (Implies(cond, exp)(cond.pos, cond.info, cond.errT), cc) // Won't recurse into exp's children
  }, Condition(), Traverse.TopDown).recurseFunc({
    case e: Exp if alreadySeen.contains(e) => Nil
    case exp: Exp if exp.isPure => Nil  // Don't recurse into pure expressions
    case _: AccessPredicate => Nil  // Don't recurse into accessibility predicates
    case f: Forall => f.exp :: Nil  // Don't recurse into triggers
    case e: Exists => e.exp :: Nil  // Don't recurse into triggers
    case l: Let => l.body :: Nil  // Don't recurse into bound expression

  })

  // Rewrite impure ternary expressions to a conjuction of implications in order to be able to use the implication
  // rewriter above.
  private val ternaryRewriter = ViperStrategy.Slim{
    case ce@CondExp(cond, tExp, fExp)
        if (!tExp.isPure || !fExp.isPure) && !Expressions.containsPermissionIntrospection(cond) =>
      And(Implies(cond, tExp)(ce.pos, ce.info, ce.errT),
        Implies(Not(cond)(cond.pos, cond.info, cond.errT), fExp)(ce.pos, ce.info, ce.errT))(ce.pos, ce.info, ce.errT)
  }

  /** Conservatively transforms all conditional accessibility predicates in `root` into unconditional accessibility
    * predicates with suitable conditional permission expressions when this is safe to do.
    */
  def rewrite(root: Program, allowTernaryWildcardsInFunctions: Boolean): Program = {
    val noTernaryProgram: Program = ternaryRewriter.execute(root)
    val functionRewriter = rewriter(root, allowTernaryWildcardsInFunctions, new mutable.HashSet[Exp]())
    val nonFunctionRewriter = rewriter(root, false, new mutable.HashSet[Exp]())
    val res = noTernaryProgram.copy(functions = noTernaryProgram.functions.map(functionRewriter.execute[Function](_)),
      predicates = noTernaryProgram.predicates.map(nonFunctionRewriter.execute[Predicate](_)),
      methods = noTernaryProgram.methods.map(nonFunctionRewriter.execute[Method](_)))(noTernaryProgram.pos, noTernaryProgram.info, noTernaryProgram.errT)
    res
  }

  /** Convenient factory for a node CondExp(cond, perm). */
  private def makeCondExp(cond: Exp, perm: Exp, elsePerm: Exp = NoPerm()()): CondExp = {
    CondExp(cond, perm, elsePerm)(perm.pos, perm.info, perm.errT)
  }

  /** Makes `acc`'s permissions conditional w.r.t. `cond`.
    */
  private def conditionalize(acc: AccessPredicate, cond: Condition, isFunction: Boolean)(implicit p: Program): Exp = {
    // We have to be careful not to introduce well-definedness issues when conditionalizing.
    // For example, if we transform
    // i >= 0 && i < |s| ==> acc(s[i].f)
    // to
    // acc(s[i].f, i >= 0 && i < |s| ? write : none)
    // then backends may complain that s[i].f is not well-defined. Thus, we only perform the
    // transformation if receiver/argument expressions are always well-defined.
    val defaultPerm = if (isFunction) WildcardPerm()() else FullPerm()()
    acc match {
      case FieldAccessPredicate(loc, perm) =>
        if (Expressions.proofObligations(loc.rcv)(p).isEmpty) {
          FieldAccessPredicate(loc, Some(makeCondExp(cond.exp, perm.getOrElse(defaultPerm))))(acc.pos, acc.info, acc.errT)
        } else {
          // Hack: use a conditional null as the receiver, that's always well-defined.
          val fieldAccess = loc.copy(rcv = makeCondExp(cond.exp, loc.rcv, NullLit()()))(loc.pos, loc.info, loc.errT)
          FieldAccessPredicate(fieldAccess, Some(makeCondExp(cond.exp, perm.getOrElse(defaultPerm))))(acc.pos, acc.info, acc.errT)
        }
      case PredicateAccessPredicate(loc, perm) =>
        if (!loc.args.exists(a => Expressions.proofObligations(a)(p).nonEmpty))
          PredicateAccessPredicate(loc, Some(makeCondExp(cond.exp, perm.getOrElse(defaultPerm))))(acc.pos, acc.info, acc.errT)
        else
          Implies(cond.exp, acc)(acc.pos, acc.info, acc.errT)
      case wand: MagicWand =>
        // Since wands do not have permission amounts, we cannot conditionalize them;
        // in order to be able to support programs with wands at all, we just write an implication.
        Implies(cond.exp, wand)(acc.pos, acc.info, acc.errT)
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
