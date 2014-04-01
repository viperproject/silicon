package semper
package silicon
package ast

import sil.verifier.VerificationError
import sil.verifier.errors.Internal
import sil.verifier.reasons.FeatureUnsupported

object Consistency {
  def check(root: Node) =
    checkQuantifiedLocationExpressions(root)

  def checkQuantifiedLocationExpressions(root: Node): Seq[VerificationError] = {
    def report(offendingNode: Node) = {
      val message = (
          "Foralls with access predicates in their body must have a special shape. "
        + "Try 'forall x: Ref :: x in aSet ==> acc(x.f, perms)' or "
        + "'forall i: Int :: i in [0..|aSeq|) ==> acc(aSeq[i].f, perms)'.")

      Internal(offendingNode, FeatureUnsupported(offendingNode, message))
    }

    root.reduceTree[Seq[VerificationError]]((n, errors) => n match {
      case ast.Forall(_, _, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(rcvr, _), _))) =>
        val error =
          rcvr match {
            case ast.SeqAt(_, i) => cond match {
              case ast.SeqIn(j, ast.SeqRanged(a, b)) if i == j => None
              case _ => Some(report(cond))
            }
            case v: ast.Variable => None
            case _ => Some(report(rcvr))
          }

        error.toSeq ++ errors.flatten

      case e: ast.Forall if !e.isPure =>
        report(e) +: errors.flatten

      case _ => errors.flatten
    })
  }
//    case _: LocationAccess => true
//  }

// helper.transform(..., cond)
  // cond match {
    // SeqIn(SeqRanged(a, b), c) if c == i => MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(s, b), a)))
    // _ => error    'forall i:Int :: i in [x..y] ==>' ...


  // Consumer
//  case ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(locacc @ ast.FieldAccess(eRcvr, f), loss))) =>

  // Producer
//  case fa@ ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, f), gain))) =>
}
