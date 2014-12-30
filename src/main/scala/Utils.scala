/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import silver.verifier.VerificationError
import silver.verifier.errors.Internal
import silver.verifier.reasons.{UnexpectedNode, FeatureUnsupported}
import state.DefaultContext
import state.terms._

package object utils {
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

  /* Take from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
  }

  def consumeExactRead(fp: Term, c: DefaultContext): Boolean = fp match {
    case _: WildcardPerm => false
    case v: Var => !c.constrainableARPs.contains(v)
    case PermPlus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermMinus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermTimes(t0, t1) => consumeExactRead(t0, c) && consumeExactRead(t1, c)
    case IntPermTimes(_, t1) => consumeExactRead(t1, c)
    case PermIntDiv(t0, _) => consumeExactRead(t0, c)
    case PermMin(t0 ,t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case Ite(_, t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case _ => true
  }

  /* http://www.tikalk.com/java/blog/avoiding-nothing */
  object notNothing {
    sealed trait NotNothing[-T]

    object NotNothing {
      implicit object notNothing extends NotNothing[Any]

      implicit object `\n The error is because the type parameter was resolved to Nothing`
          extends NotNothing[Nothing]
    }
  }

  object counter {
    private var value = 0

    def next() = {
      value = value + 1
      value
    }

    def reset() {
      value = 0
    }
  }

  object ast {
    def BigAnd(it: Iterable[silver.ast.Exp],
               f: silver.ast.Exp => silver.ast.Exp = e => e,
               emptyPos: silver.ast.Position = silver.ast.NoPosition) =

      mapReduceLeft(it,
                    f,
                    (e0: silver.ast.Exp, e1: silver.ast.Exp) => silver.ast.And(e0, e1)(e0.pos, e0.info),
                     silver.ast.TrueLit()(emptyPos))
  }

  object consistency {
    type PositionedNode = silver.ast.Node with silver.ast.Positioned

    def check(program: silver.ast.Program) = (
      program.functions.flatMap(checkFunctionPostconditionNotRecursive)
        ++ checkPermissions(program))

    /* Unsupported expressions, features or cases */

    def createIllegalQuantifiedLocationExpressionError(offendingNode: PositionedNode) = {
      val message = (
        "Silicon requires foralls with access predicates in their body to have "
          + "a special shape. Try 'forall x: Ref :: x in aSet ==> acc(x.f, perms)' "
          + "or 'forall i: Int :: i in [0..|aSeq|) ==> acc(aSeq[i].f, perms)'.")

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    def createUnsupportedRecursiveFunctionPostconditionError(fapp: silver.ast.FuncApp) = {
      val message = (
        "Silicon cannot handle function postconditions that mention the function itself. "
          + "Try to replace the function application by 'result'.")

      Internal(fapp, FeatureUnsupported(fapp, message))
    }

    def checkFunctionPostconditionNotRecursive(function: silver.ast.Function): Seq[VerificationError] =
    /* TODO: Most likely doesn't detect mutual recursion. */
      function.posts.flatMap(_.reduceTree[Seq[VerificationError]]((n, errors) => n match {
        case fapp @ silver.ast.FuncApp(functionName, _) if function.name == functionName =>
          createUnsupportedRecursiveFunctionPostconditionError(fapp) +: errors.flatten

        case _ => errors.flatten
      }))

    def createUnsupportedPermissionExpressionError(offendingNode: PositionedNode) = {
      val message = s"Silicon doesn't support the permission expression $offendingNode."

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    def checkPermissions(root: PositionedNode): Seq[VerificationError] =
      root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
        case eps: silver.ast.EpsilonPerm => createUnsupportedPermissionExpressionError(eps) +: errors.flatten
        case _ => errors.flatten
      })

    /* Unexpected nodes */

    def createUnexpectedInhaleExhaleExpressionError(offendingNode: PositionedNode) = {
      val explanation =
        "InhaleExhale-expressions should have been eliminated by calling expr.whenInhaling/Exhaling."

      val stackTrace = new Throwable().getStackTrace

      Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
    }

    def createUnexpectedNodeDuringDomainTranslationError(offendingNode: PositionedNode) = {
      val explanation = "The expression should not occur in domain expressions."
      val stackTrace = new Throwable().getStackTrace

      Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
    }
  }
}
