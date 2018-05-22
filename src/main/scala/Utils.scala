/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import viper.silver
import viper.silver.components.StatefulComponent
import viper.silver.verifier.{VerificationError, errors}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.{FeatureUnsupported, UnexpectedNode}
import viper.silver.ast.utility.Rewriter.Traverse
import viper.silicon.state.terms.{Sort, Term, Var}
import viper.silicon.verifier.Verifier

package object utils {
  def freshSnap: (Sort, Verifier) => Var = (sort, v) => v.decider.fresh(sort)
  def toSf(t: Term): (Sort, Verifier) => Term = (sort, _) => t.convert(sort)

  def mapReduceLeft[E](it: Iterable[E], f: E => E, op: (E, E) => E, unit: E): E =
    if (it.isEmpty)
      unit
    else
      it.map(f).reduceLeft((t1, t2) => op(t1, t2))

  def conflictFreeUnion[K, V](m1: Map[K, V], m2: Map[K, V]): Either[Seq[(K, V, V)], Map[K, V]] = {
    m1 flatMap { case (k1, v1) => m2.get(k1) match {
      case None | Some(`v1`) => None
      case Some(v2) => Some((k1, v1, v2))
    }} match {
      case Seq() => Right(m1 ++ m2)
      case conflicts => Left(conflicts.toSeq)
    }
  }

  def append[K1,       E1,       C1 <: Iterable[E1],
             K2 <: K1, E2 <: E1, C2 <: C1]
            (m1: Map[K1, C1],
             m2: Map[K2, C2],
             app: (C1, C2) => C1) = {

    m2.foldLeft(m1) { case (m1Acc, (k2, c2)) =>
      val c3 = m1Acc.get(k2).fold(c2: C1)(c1 => app(c1, c2))
      m1Acc + (k2 -> c3)
    }
  }

  /* NOT thread-safe */
  class Counter(firstValue: Int = 0)
      extends StatefulComponent
         with Cloneable {

    private var nextValue = firstValue

    def next() = {
      val n = nextValue
      nextValue = nextValue + 1

      n
    }

    /* Lifetime */

    def start() {}
    def stop() {}

    def reset() {
      nextValue = firstValue
    }

    override def clone(): Counter = {
      val clonedCounter = new Counter(firstValue)
      clonedCounter.nextValue = nextValue

      clonedCounter
    }
  }

  /* A base implementation of start/reset/stop is required by the
   * DefaultElementVerifier, Scala will (rightfully) complain otherwise.
   */
  class NoOpStatefulComponent extends StatefulComponent {
    @inline def start() {}
    @inline def reset() {}
    @inline def stop() {}
  }

  trait MustBeReinitializedAfterReset { this: StatefulComponent => }

  /* http://www.tikalk.com/java/blog/avoiding-nothing */
  object notNothing {
    sealed trait NotNothing[-T]

    object NotNothing {
      implicit object notNothing extends NotNothing[Any]

      implicit object `\n The error is because the type parameter was resolved to Nothing`
          extends NotNothing[Nothing]
    }
  }

  object ast {
    /** Use with care! In particular, be sure you know the effect of `BigAnd` on
      * snapshot recording before you e.g. `consume(..., BigAnd(some_preconditions), ...)`.
      * Consider using `consumes(..., some_preconditions, ...)` instead.
      */
    def BigAnd(it: Iterable[silver.ast.Exp],
               f: silver.ast.Exp => silver.ast.Exp = e => e,
               emptyPos: silver.ast.Position = silver.ast.NoPosition) =

      mapReduceLeft(it,
                    f,
                    (e0: silver.ast.Exp, e1: silver.ast.Exp) => silver.ast.And(e0, e1)(e0.pos, e0.info),
                     silver.ast.TrueLit()(emptyPos))

    def BigOr(it: Iterable[silver.ast.Exp],
               f: silver.ast.Exp => silver.ast.Exp = e => e,
               emptyPos: silver.ast.Position = silver.ast.NoPosition) =

      mapReduceLeft(it,
                    f,
                    (e0: silver.ast.Exp, e1: silver.ast.Exp) => silver.ast.Or(e0, e1)(e0.pos, e0.info),
                     silver.ast.FalseLit()(emptyPos))

    /** Note: be aware of Silver issue #95!*/
    def rewriteRangeContains(program: silver.ast.Program): silver.ast.Program =
      program.transform({
        case e @ silver.ast.SeqContains(x, silver.ast.RangeSeq(a, b)) =>
          silver.ast.And(
            silver.ast.LeCmp(a, x)(e.pos),
            silver.ast.LtCmp(x, b)(e.pos)
          )(e.pos)
      }, Traverse.TopDown)

    /** Aims to compute triggers for the given quantifier `forall` by successively trying
      * different strategies.
      *
      * Attention: This method is *not* thread-safe, because it uses
      * [[silver.ast.utility.Triggers.TriggerGeneration]] , which is itself not thread-safe.
      *
      * @param forall The quantifier to compute triggers for.
      * @return A quantifier that is equal to the input quantifier, except potentially for triggers.
      */
    def autoTrigger(forall: silver.ast.Forall): silver.ast.Forall = {
      val defaultTriggerForall = forall.autoTrigger

      val autoTriggeredForall =
        if (defaultTriggerForall.triggers.nonEmpty)
          /* Standard trigger generation code succeeded */
          defaultTriggerForall
        else {
          /* Standard trigger generation code failed.
           * Let's try generating (certain) invalid triggers, which will then be rewritten
           */
          silver.ast.utility.Triggers.TriggerGeneration.setCustomIsForbiddenInTrigger {
            case _: silver.ast.Add | _: silver.ast.Sub => false
          }

          val optTriggerSet = silver.ast.utility.Expressions.generateTriggerSet(forall)

          silver.ast.utility.Triggers.TriggerGeneration.setCustomIsForbiddenInTrigger(PartialFunction.empty)

          val advancedTriggerForall =
            optTriggerSet match {
              case Some((variables, triggerSets)) =>
                /* Invalid triggers could be generated, now try to rewrite them */
                val intermediateForall = silver.ast.Forall(variables, Nil, forall.exp)(forall.pos, forall.info)
                silver.ast.utility.Triggers.AxiomRewriter.rewrite(intermediateForall, triggerSets).getOrElse(forall)
              case None =>
                /* Invalid triggers could not be generated -> give up */
                forall
            }

          advancedTriggerForall
        }

      autoTriggeredForall
    }

    def sourceLine(node: silver.ast.Node with silver.ast.Positioned): String = node.pos match {
      case pos: silver.ast.HasLineColumn => pos.line.toString
      case _ => node.pos.toString
    }

    def sourceLineColumn(node: silver.ast.Node with silver.ast.Positioned): String = node.pos match {
      case pos: silver.ast.HasLineColumn => s"${pos.line}:${pos.column}"
      case _ => node.pos.toString
    }
  }

  object consistency {
    type ErrorNode = silver.ast.Node with silver.ast.Positioned with silver.ast.TransformableErrors

    def check(program: silver.ast.Program) = (
         checkPermissions(program)
      ++ program.members.flatMap(m => checkFieldAccessesInTriggers(m, program))
      ++ checkInhaleExhaleAssertions(program))

    def createUnsupportedPermissionExpressionError(offendingNode: errors.ErrorNode) = {
      val message = s"Silicon doesn't support the permission expression $offendingNode."

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    def checkPermissions(root: ErrorNode): Seq[VerificationError] =
      root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
        case eps: silver.ast.EpsilonPerm => createUnsupportedPermissionExpressionError(eps) +: errors.flatten
        case _ => errors.flatten
      })

    def createUnsupportedFieldAccessInTrigger(offendingNode: silver.ast.FieldAccess) = {
      val message = (   "Silicon only supports field accesses as triggers if (1) permissions to the "
                     +  "field come from quantified permissions, and if (2) the field access also "
                     + s"occurs in the body of the quantification. $offendingNode is not such a "
                     +  "field access.")

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    def checkFieldAccessesInTriggers(root: silver.ast.Member, program: silver.ast.Program)
                                    : Seq[VerificationError] = {

      val quantifiedFields = silver.ast.utility.QuantifiedPermissions.quantifiedFields(root, program)

      root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
        case forall: silver.ast.Forall =>
          val qvars = forall.variables.map(_.localVar)

          forall.triggers.flatMap { ts =>
            ts.exps.flatMap(_.collect {
              case fa: silver.ast.FieldAccess
                   if qvars.exists(fa.contains) &&
                      !(quantifiedFields.contains(fa.field) && forall.exp.contains(fa))
                => fa
            })
          } match {
            case Seq() => errors.flatten
            case fas => (fas map createUnsupportedFieldAccessInTrigger) ++ errors.flatten
          }

        case _ => errors.flatten
      })
    }

    def createUnsupportedInhaleExhaleAssertion(offendingNode: silver.ast.InhaleExhaleExp) = {
      val message = (   "Silicon currently doesn't support inhale-exhale assertions in certain "
                     +  "positions. See Silicon issue #271 for further details.")

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    def checkInhaleExhaleAssertions(root: ErrorNode): Seq[VerificationError] = {
      def collectInhaleExhaleAssertions(root: ErrorNode): Seq[silver.ast.InhaleExhaleExp] =
        root.deepCollect{case ie: silver.ast.InhaleExhaleExp if !ie.isPure => ie}

      root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
        case fun: silver.ast.Function =>
          val newErrs = fun.pres.flatMap(collectInhaleExhaleAssertions)
                                .map(createUnsupportedInhaleExhaleAssertion)
          newErrs ++ errors.flatten
        case pred: silver.ast.Predicate if pred.body.nonEmpty =>
          val newErrs = collectInhaleExhaleAssertions(pred.body.get)
                          .map(createUnsupportedInhaleExhaleAssertion)
          newErrs ++ errors.flatten
        case _ => errors.flatten
      })
    }

    /* Unexpected nodes */

    def createUnexpectedInhaleExhaleExpressionError(offendingNode: errors.ErrorNode) = {
      val explanation =
        "InhaleExhale-expressions should have been eliminated by calling expr.whenInhaling/Exhaling."

      val stackTrace = new Throwable().getStackTrace

      Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
    }

    def createUnexpectedNodeDuringDomainTranslationError(offendingNode: errors.ErrorNode) = {
      val explanation = "The expression should not occur in domain expressions."
      val stackTrace = new Throwable().getStackTrace

      Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
    }
  }
}
