// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{And, Forall, Implies, Quantification, Term, Trigger, Var}
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast
import viper.silver.ast.utility.Expressions

import scala.collection.mutable

/**
  * An assumption of the form `guards ==> forall vars :: body` that the user can instantiate; see
  * [[SiliconDebugSession.instantiate]].
  *
  * @param eGuards the guards as Viper expressions, if all of them are known.
  * @param eVars   the bound variables as Viper declarations, if known.
  * @param eBody   the body as a Viper expression, if known.
  */
case class InstantiableForall(guards: Seq[Term],
                              eGuards: Option[Seq[ast.Exp]],
                              vars: Seq[Var],
                              eVars: Option[Seq[ast.LocalVarDecl]],
                              body: Term,
                              eBody: Option[ast.Exp],
                              triggers: Seq[Trigger]) {

  /** The names of the bound variables, as the user sees them. */
  def varNames: Seq[String] = eVars.map(_.map(_.name)).getOrElse(vars.map(_.id.name))

  /**
    * The instance for `args`, which replace the first bound variables; the instance is quantified over the remaining
    * ones, if any.
    */
  def instantiate(args: Seq[Term]): Term = {
    val (instantiated, remaining) = vars.splitAt(args.size)
    val instance = body.replace(instantiated, args)
    val quantified =
      if (remaining.isEmpty) instance
      else Quantification(Forall, remaining, instance, triggers.map(t => Trigger(t.p.map(_.replace(instantiated, args)))))
    Implies(And(guards), quantified)
  }

  /** The counterpart of [[instantiate]] for Viper expressions, if the expressions of this quantifier are known. */
  def instantiateExp(args: Seq[ast.Exp]): Option[ast.Exp] =
    for (gs <- eGuards; vs <- eVars; b <- eBody) yield {
      val (instantiated, remaining) = vs.splitAt(args.size)
      val instance = Expressions.instantiateVariables(b, instantiated, args, Set.empty[String])
      val quantified = if (remaining.isEmpty) instance else ast.Forall(remaining, Seq.empty, instance)()
      if (gs.isEmpty) quantified else ast.Implies(BigAnd(gs), quantified)()
    }
}

object InstantiableForall {

  /**
    * The assumption with id `id` among `assumptions`, if it is a universally quantified one, or else why it cannot be
    * instantiated.
    *
    * The assumption may be nested in others. Under an implication, it only holds if the implication's condition does,
    * which then becomes a guard of the quantifier. Under a quantifier, it may refer to the quantifier's variables, so
    * it cannot be instantiated on its own.
    */
  def find(assumptions: InsertionOrderedSet[DebugExp], id: Int): Either[String, InstantiableForall] = {
    val visited = mutable.HashSet.empty[DebugExp]

    def search(de: DebugExp, guards: Seq[(Term, Option[ast.Exp])], enclosingQuantifier: Option[Int])
              : Option[Either[String, InstantiableForall]] = {
      if (!visited.add(de)) None
      else if (de.id == id) Some(enclosingQuantifier match {
        case Some(q) =>
          Left(s"[$id] is nested in the quantifier [$q] and may refer to its variables; instantiate [$q] instead.")
        case None =>
          of(de).map(f => f.copy(
            guards = guards.map(_._1) ++ f.guards,
            eGuards = for (gs <- sequence(guards.map(_._2)); fgs <- f.eGuards) yield gs ++ fgs
          )).toRight(s"[$id] is not a universally quantified assumption (forall).")
      })
      else {
        val (innerGuards, innerQuantifier) = de match {
          case i: ImplicationDebugExp if i.term.isDefined => (guards :+ (i.term.get -> i.finalExp), enclosingQuantifier)
          case q: QuantifiedDebugExp => (guards, enclosingQuantifier.orElse(Some(q.id)))
          case _ => (guards, enclosingQuantifier)
        }
        de.children.iterator.map(search(_, innerGuards, innerQuantifier)).collectFirst { case Some(r) => r }
      }
    }

    assumptions.iterator.map(search(_, Seq.empty, None)).collectFirst { case Some(r) => r }
      .getOrElse(Left(s"There is no assumption with id $id."))
  }

  /** Whether `de` is a universally quantified assumption; like `of(de).isDefined`, but cheaper. */
  def isForall(de: DebugExp): Boolean = de match {
    case q: QuantifiedDebugExp => q.quantifier == Forall.toString && q.tQvars.nonEmpty
    case _ => of(de).isDefined
  }

  /** The universally quantified assumption `de` is, if it is one, irrespective of where it is nested. */
  def of(de: DebugExp): Option[InstantiableForall] = de match {
    case q: QuantifiedDebugExp if q.quantifier == Forall.toString && q.tQvars.nonEmpty =>
      val eVars = q.qvars.collect { case v: ast.AbstractLocalVar => ast.LocalVarDecl(v.name, v.typ)() }
      val body = And(q.children.toSeq.flatMap(_.getAllTerms(mutable.HashSet.empty)))
      Some(InstantiableForall(Seq.empty, Some(Seq.empty), q.tQvars, Option.when(eVars.size == q.qvars.size)(eVars),
        body, None, q.tTriggers))
    case _: QuantifiedDebugExp | _: ImplicationDebugExp => None
    case _ => de.term.flatMap(ofTerm(_, de.finalExp))
  }

  private def ofTerm(t: Term, e: Option[ast.Exp]): Option[InstantiableForall] = t match {
    case q: Quantification if q.q == Forall =>
      val (eVars, eBody) = e match {
        case Some(f: ast.Forall) if f.variables.size == q.vars.size => (Some(f.variables), Some(f.exp))
        case _ => (None, None)
      }
      Some(InstantiableForall(Seq.empty, Some(Seq.empty), q.vars, eVars, q.body, eBody, q.triggers))
    case Implies(guard, rest) =>
      val (eGuard, eRest) = e match {
        case Some(ast.Implies(l, r)) => (Some(l), Some(r))
        case _ => (None, None)
      }
      ofTerm(rest, eRest).map(f =>
        f.copy(guards = guard +: f.guards, eGuards = for (g <- eGuard; gs <- f.eGuards) yield g +: gs))
    case And(ts) =>
      // Each conjunct holds, so a quantifier among them can be instantiated, as long as it is clear which one is meant.
      ts.flatMap(ofTerm(_, None)) match {
        case Seq(f) => Some(f)
        case _ => None
      }
    case _ => None
  }

  private def sequence[A](options: Seq[Option[A]]): Option[Seq[A]] =
    if (options.forall(_.isDefined)) Some(options.map(_.get)) else None
}
