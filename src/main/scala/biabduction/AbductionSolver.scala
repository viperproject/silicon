package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.utils.ast.BigAnd
import viper.silver.ast.{Exp, Implies, TrueLit}
import viper.silver.verifier.DummyReason
import viper.silver.verifier.errors.Internal

object AbductionSolver {

  private val rules = Seq(AccessPredicateRemove, Match, ListFoldBase, ListFold, ListUnfold, AccessPredicateMissing)

  def solve(q: SiliconAbductionQuestion): String = {
    val fail = Failure(Internal().dueTo(DummyReason))
    var result = ""


    applyRule(q, 0) { q1 => {
      if (q1.goal.isEmpty) {

        val bcs = BigAnd(q.v.decider.pcs.branchConditionExps.collect { case Some(e) if q.transformToInputs(e).isDefined => q.transformToInputs(e).get })

        val rt = q1.foundPrecons.map { (e: Exp) =>
          (q.transformToInputs(e), bcs) match {
            case (Some(e1), TrueLit()) => e1.toString()
            case (Some(e1), bcs) => Implies(bcs, e1)().toString()
            case _ => "Could not be transformed to inputs: " + e.toString()
          }
        }.mkString("\n")
        result = "Abduction successful.\nAbduced preconditions:\n" + rt + "\nAbduced statements:\n" + q1.foundStmts.map(_.toString()).mkString("\n")
      } else {
        result = "Abduction failed."
      }
      fail
    }
    }
    result
  }

  /**
    * Recursively applies the abduction rules until we reach the end of the rules list. If the goal is empty, we were
    * successful.
    */
  private def applyRule(q: SiliconAbductionQuestion, rule: Int)(Q: SiliconAbductionQuestion => VerificationResult): VerificationResult = {
    rules(rule).checkAndApply(q, rule)((q1, r1) => {
      if (r1 == rules.length) {
        Q(q1)
      } else {
        applyRule(q1, r1)(Q)
      }
    })
  }
}
