package semper
package silicon
package ast

import sil.verifier.VerificationError
import sil.verifier.errors.Internal
import sil.verifier.reasons.FeatureUnsupported

object Consistency {
  def check(program: Program) = (
       checkQuantifiedLocationExpressions(program)
    ++ program.functions.flatMap(checkFunctionPostconditionNotRecursive)
    ++ checkPermissions(program))

  def reportIllegalQuantifiedLocationExpression(offendingNode: Node) = {
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
              case _ => Some(reportIllegalQuantifiedLocationExpression(cond))
            }
            case v: ast.Variable => None
            case _ => Some(reportIllegalQuantifiedLocationExpression(rcvr))
          }

        error.toSeq ++ errors.flatten

      case e: ast.Forall if !e.isPure =>
        reportIllegalQuantifiedLocationExpression(e) +: errors.flatten

      case _ => errors.flatten
    })
  }

  def reportUnsupportedRecursiveFunctionPostcondition(fapp: FuncApp) = {
    val message = (
      "Silicon cannot handle function postconditions that mention the function itself. "
        + "Try to replace the function application by 'result'.")

    Internal(fapp, FeatureUnsupported(fapp, message))
  }

  def checkFunctionPostconditionNotRecursive(function: ProgramFunction): Seq[VerificationError] =
    /* TODO: Most likely doesn't detect mutual recursion. */
    function.posts.flatMap(_.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case fapp @ FuncApp(someFunc, _) if function.name == someFunc.name =>
        reportUnsupportedRecursiveFunctionPostcondition(fapp) +: errors.flatten

      case _ => errors.flatten
    }))

  def reportUnsupportedPermissionExpressions(offendingNode: Node) = {
    val message = s"Silicon doesn't support the permission expression $offendingNode."

    Internal(offendingNode, FeatureUnsupported(offendingNode, message))
  }

  def checkPermissions(root: Node): Seq[VerificationError] =
    root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case eps: ast.EpsilonPerm => reportUnsupportedPermissionExpressions(eps) +: errors.flatten
      case _ => errors.flatten
    })

  /* TODO: Implement a corresponding check-method. Currently, the check is
   *       done during the verification, see DefaultEvaluator.
   */
  def reportUnsupportedPredicateRecursion(offendingNode: Node) = {
    val message = (
        "Recursion that does not go through a function, e.g., a predicate such as "
      + "P {... && (x.next != null ==> acc(P(x.next)) && unfolding acc(P(x.next)) in e)} "
      + "is currently not supported in Silicon. Try wrapping "
      + "'unfolding acc(P(x.next)) in e' in a function, and invoking the function "
      + "from the predicate body.")

    Internal(offendingNode, FeatureUnsupported(offendingNode, message))
  }
}
