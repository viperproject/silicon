package viper.silicon.biabduction

import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.verifier.Verifier
import viper.silver.ast.Exp

object AbductionSolver {

  private val rules = Seq(AccessPredicateRemove, Match, FoldBase, Fold, Unfold, AccessPredicateMissing)

  def solve(s: State, v: Verifier, fail: VerificationResult, missing: Exp): VerificationResult = {
    applyRule(AbductionQuestion(s, v, Seq(missing), Seq()), 0)(fail)
  }

  /**
    * Recursively applies the abduction rules until we reach the end of the rules list. If the goal is empty, we were
    * successful.
    */
  private def applyRule(q: AbductionQuestion, rule: Int)(Q: VerificationResult): VerificationResult = {
    rules(rule).checkAndApply(q, rule)((q1, r1) => {
      if (r1 == rules.length) {
        if (q.goal.isEmpty) {
          println("Abduction successful. Found preconditions:")
          for (q <- q.result) println(q.toString())
        } else {
          println("Abduction failed.")
        }
        Q
      } else {
        applyRule(q1, r1)(Q)
      }
    })
  }
}
