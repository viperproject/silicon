// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.state.terms.{And, Exists, Forall, Implies, Quantification, Quantifier, Term, Trigger, Var}
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast
import viper.silver.ast.utility.Expressions

import scala.collection.mutable

/**
  * An assumption of the form `guards ==> forall vars :: body` or `guards ==> exists vars :: body`, which the user can
  * instantiate (see [[SiliconDebugSession.instantiate]]) or obtain a witness of (see
  * [[SiliconDebugSession.obtainWitness]]), respectively.
  *
  * @param eGuards the guards as Viper expressions, if all of them are known.
  * @param eVars   the bound variables as Viper declarations, if known.
  * @param eBody   the body as a Viper expression, if known.
  */
case class QuantifiedAssumption(quantifier: Quantifier,
                                guards: Seq[Term],
                                eGuards: Option[Seq[ast.Exp]],
                                vars: Seq[Var],
                                eVars: Option[Seq[ast.LocalVarDecl]],
                                body: Term,
                                eBody: Option[ast.Exp],
                                triggers: Seq[Trigger]) {

  /** The names of the bound variables, as the user sees them. */
  def varNames: Seq[String] = eVars.map(_.map(_.name)).getOrElse(vars.map(_.id.name))

  /**
    * The body for `args`, which replace the first bound variables, under the guards; the result is still quantified
    * over the remaining variables, if any.
    */
  def instantiate(args: Seq[Term]): Term = {
    val (instantiated, remaining) = vars.splitAt(args.size)
    val instance = body.replace(instantiated, args)
    val quantified =
      if (remaining.isEmpty) instance
      else Quantification(quantifier, remaining, instance, triggers.map(t => Trigger(t.p.map(_.replace(instantiated, args)))))
    Implies(And(guards), quantified)
  }

  /** The counterpart of [[instantiate]] for Viper expressions, if the expressions of this quantifier are known. */
  def instantiateExp(args: Seq[ast.Exp]): Option[ast.Exp] =
    for (gs <- eGuards; vs <- eVars; b <- eBody) yield {
      val (instantiated, remaining) = vs.splitAt(args.size)
      val instance = Expressions.instantiateVariables(b, instantiated, args, Set.empty[String])
      val quantified =
        if (remaining.isEmpty) instance
        else if (quantifier == Forall) ast.Forall(remaining, Seq.empty, instance)()
        else ast.Exists(remaining, Seq.empty, instance)()
      if (gs.isEmpty) quantified else ast.Implies(BigAnd(gs), quantified)()
    }
}

object QuantifiedAssumption {

  /**
    * The assumption with id `id` among `assumptions`, if it is a quantified one, or else why it is not.
    *
    * The assumption may be nested in others. Under an implication, it only holds if the implication's condition does,
    * which then becomes a guard of the quantifier. Under a quantifier, it may refer to the quantifier's variables, so
    * it cannot be used on its own.
    */
  def find(assumptions: InsertionOrderedSet[DebugExp], id: Int): Either[String, QuantifiedAssumption] = {
    val visited = mutable.HashSet.empty[DebugExp]

    def search(de: DebugExp, guards: Seq[(Term, Option[ast.Exp])], enclosingQuantifier: Option[Int])
              : Option[Either[String, QuantifiedAssumption]] = {
      if (!visited.add(de)) None
      else if (de.id == id) Some(enclosingQuantifier match {
        case Some(q) =>
          Left(s"[$id] is nested in the quantifier [$q] and may refer to its variables; use [$q] instead.")
        case None =>
          of(de).map(q => q.copy(
            guards = guards.map(_._1) ++ q.guards,
            eGuards = for (gs <- sequence(guards.map(_._2)); qgs <- q.eGuards) yield gs ++ qgs
          )).toRight(s"[$id] is not a quantified assumption (forall or exists).")
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

  /** The quantifier of `de`, if it is a quantified assumption; like `of(de).map(_.quantifier)`, but cheaper. */
  def quantifierOf(de: DebugExp): Option[Quantifier] = de match {
    case q: QuantifiedDebugExp => quantifierNamed(q.quantifier).filter(_ => q.tQvars.nonEmpty)
    case _ => of(de).map(_.quantifier)
  }

  /** The quantified assumption `de` is, if it is one, irrespective of where it is nested. */
  def of(de: DebugExp): Option[QuantifiedAssumption] = de match {
    case q: QuantifiedDebugExp if q.tQvars.nonEmpty && quantifierNamed(q.quantifier).isDefined =>
      val eVars = q.qvars.collect { case v: ast.AbstractLocalVar => ast.LocalVarDecl(v.name, v.typ)() }
      val body = And(q.children.toSeq.flatMap(_.getAllTerms(mutable.HashSet.empty)))
      Some(QuantifiedAssumption(quantifierNamed(q.quantifier).get, Seq.empty, Some(Seq.empty), q.tQvars,
        Option.when(eVars.size == q.qvars.size)(eVars), body, None, q.tTriggers))
    case _: QuantifiedDebugExp | _: ImplicationDebugExp => None
    case _ => de.term.flatMap(ofTerm(_, de.finalExp))
  }

  /** `QuantifiedDebugExp.quantifier` is the name of a [[Quantifier]]. */
  private def quantifierNamed(name: String): Option[Quantifier] = Seq(Forall, Exists).find(_.toString == name)

  private def ofTerm(t: Term, e: Option[ast.Exp]): Option[QuantifiedAssumption] = t match {
    case q: Quantification if q.q == Forall || q.q == Exists =>
      val (eVars, eBody) = e match {
        case Some(f: ast.QuantifiedExp) if f.variables.size == q.vars.size => (Some(f.variables), Some(f.exp))
        case _ => (None, None)
      }
      Some(QuantifiedAssumption(q.q, Seq.empty, Some(Seq.empty), q.vars, eVars, q.body, eBody, q.triggers))
    case Implies(guard, rest) =>
      val (eGuard, eRest) = e match {
        case Some(ast.Implies(l, r)) => (Some(l), Some(r))
        case _ => (None, None)
      }
      ofTerm(rest, eRest).map(q =>
        q.copy(guards = guard +: q.guards, eGuards = for (g <- eGuard; gs <- q.eGuards) yield g +: gs))
    case And(ts) =>
      // Each conjunct holds, so a quantifier among them can be used, as long as it is clear which one is meant.
      ts.flatMap(ofTerm(_, None)) match {
        case Seq(q) => Some(q)
        case _ => None
      }
    case _ => None
  }

  private def sequence[A](options: Seq[Option[A]]): Option[Seq[A]] =
    if (options.forall(_.isDefined)) Some(options.map(_.get)) else None
}
