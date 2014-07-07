/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper
package silicon
package ast

import sil.verifier.{AbstractVerificationError, VerificationError}
import sil.verifier.errors.Internal
import sil.verifier.reasons.{UnexpectedNode, FeatureUnsupported}

object Consistency {
  def check(program: Program) = (
       checkQuantifiedLocationExpressions(program)
    ++ program.functions.flatMap(checkFunctionPostconditionNotRecursive)
    ++ checkPermissions(program))

  /* Unsupported expressions, features or cases */

  def createIllegalQuantifiedLocationExpressionError(offendingNode: Node) = {
    val message = (
        "Silicon requires foralls with access predicates in their body to have "
      + "a special shape. Try 'forall x: Ref :: x in aSet ==> acc(x.f, perms)' "
      + "or 'forall i: Int :: i in [0..|aSeq|) ==> acc(aSeq[i].f, perms)'.")

    Internal(offendingNode, FeatureUnsupported(offendingNode, message))
  }

  def checkQuantifiedLocationExpressions(root: Node): Seq[VerificationError] = {
    /* The constraints imposed on the shape of quantified permission
     * expressions are the same that Korbinian imposed in DefaultProducer,
     * DefaultConsumer and QuantifiedChunkHelper.
     */

    root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case ast.Forall(_, _, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(rcvr, _), _))) =>
        val error =
          rcvr match {
            case ast.SeqAt(_, i) => cond match {
              case ast.SeqIn(j, ast.SeqRanged(a, b)) if i == j => None
              case _ => Some(createIllegalQuantifiedLocationExpressionError(cond))
            }
            case v: ast.Variable => None
            case _ => Some(createIllegalQuantifiedLocationExpressionError(rcvr))
          }

        error.toSeq ++ errors.flatten

      case e: ast.Forall if !e.isPure =>
        createIllegalQuantifiedLocationExpressionError(e) +: errors.flatten

      case _ => errors.flatten
    })
  }

  def createUnsupportedRecursiveFunctionPostconditionError(fapp: FuncApp) = {
    val message = (
      "Silicon cannot handle function postconditions that mention the function itself. "
        + "Try to replace the function application by 'result'.")

    Internal(fapp, FeatureUnsupported(fapp, message))
  }

  def checkFunctionPostconditionNotRecursive(function: ProgramFunction): Seq[VerificationError] =
    /* TODO: Most likely doesn't detect mutual recursion. */
    function.posts.flatMap(_.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case fapp @ FuncApp(functionName, _) if function.name == functionName =>
        createUnsupportedRecursiveFunctionPostconditionError(fapp) +: errors.flatten

      case _ => errors.flatten
    }))

  def createUnsupportedPermissionExpressionError(offendingNode: Node) = {
    val message = s"Silicon doesn't support the permission expression $offendingNode."

    Internal(offendingNode, FeatureUnsupported(offendingNode, message))
  }

  def checkPermissions(root: Node): Seq[VerificationError] =
    root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case eps: ast.EpsilonPerm => createUnsupportedPermissionExpressionError(eps) +: errors.flatten
      case _ => errors.flatten
    })

  /* TODO: Implement a corresponding check-method. Currently, the check is
   *       done during the verification, see DefaultEvaluator.
   */
  def createUnsupportedPredicateRecursionError(offendingNode: Node) = {
    val message = (
        "Recursion that does not go through a function, e.g., a predicate such as "
      + "P {... && (x.next != null ==> acc(P(x.next)) && unfolding acc(P(x.next)) in e)} "
      + "is currently not supported in Silicon. Try wrapping "
      + "'unfolding acc(P(x.next)) in e' in a function, and invoking the function "
      + "from the predicate body.")

    Internal(offendingNode, FeatureUnsupported(offendingNode, message))
  }

  /* Unexpected nodes */

  def createUnexpectedInhaleExhaleExpressionError(offendingNode: Node) = {
    val explanation =
      "InhaleExhale-expressions should have been eliminated by calling expr.whenInhaling/Exhaling."

    val stackTrace = new Throwable().getStackTrace

    Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
  }

  def createUnexpectedNodeDuringDomainTranslationError(offendingNode: Node) = {
    val explanation = "The expression should not occur in domain expressions."
    val stackTrace = new Throwable().getStackTrace

    Internal(offendingNode, UnexpectedNode(offendingNode, explanation, stackTrace))
  }
}
