/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package supporters

import interfaces.{Success, VerificationResult}
import interfaces.decider.Decider
import interfaces.state.{State, PathConditions, Heap, Store, Context}
import state.DefaultContext
import state.terms.{Apply, sorts, True, Implies, And, Term, Sort}

trait Joiner[C <: Context[C]] {
  def join(joinSort: Sort, joinFunctionName: String, joinFunctionArgs: Seq[Term], c: C)
          (block: ((Term, C) => VerificationResult) => VerificationResult)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult
}

trait DefaultJoiner[ST <: Store[ST],
                    H <: Heap[H],
                    PC <: PathConditions[PC],
                    S <: State[ST, H, S]]
    extends Joiner[DefaultContext]
{ this: DefaultBrancher[ST, H, PC, S] =>

  private[this] type C = DefaultContext

  val decider: Decider[ST, H, PC, S, C]

  def join(joinSort: Sort, joinFunctionName: String, joinFunctionArgs: Seq[Term], c: C)
          (block: ((Term, C) => VerificationResult) => VerificationResult)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {

    val πPre: Set[Term] = decider.π
    var localResults: List[LocalEvaluationResult] = Nil

    //    decider.pushScope()
    /* Note: Executing the block in its own scope may result in incompletenesses:
     *   1. Let A be an assumption, e.g., a combine-term, that is added during
     *      the execution of block, but before the block's execution branches
     *   2. When the leaves of the block's execution are combined, A will be placed
     *      under the guards corresponding to the individual leaves; but A should
     *      be unconditional since it was added to the path conditions before
     *      the branching took place.
     */

    val r =
      block((tR, cR) => {
        localResults ::= LocalEvaluationResult(cR.branchConditions.filterNot(c.branchConditions.contains),
                                               tR,
                                               decider.π -- πPre,
                                               cR.copy(branchConditions = c.branchConditions))
            /* TODO: Storing a copy of cR with modified branchConditions is only necessary
             *       because DefaultContext.merge (correctly) insists on equal branchConditions,
             *       which cannot be circumvented/special-cased when merging contexts here (more
             *       precisely, a bit further down via combine(localResults, ...)).
             *       See DefaultBrancher.branchAndJoin for a similar comment.
             */
        Success()
      })

    //    decider.popScope()

    r && {
      //        var tJoined: Term = null
      //        var cJoined: C = null

      localResults match {
        case List() =>
          /* Should imply that Silicon is exploring an infeasible proof branch */
          Success()

        case List(localResult) =>
          //            assert(localResult.πGuards.isEmpty,
          //                   s"Joining single branch, expected no guard, but found ${localResult.πGuards}")

          decider.assume(localResult.auxiliaryTerms)

          val tJoined = localResult.actualResult
          val cJoined = localResult.context.copy(branchConditions = c.branchConditions)
          Q(tJoined, cJoined)

        case _ =>
          val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
          val actualResultFuncSort = sorts.Arrow(quantifiedVarsSorts, joinSort)
          val summarySymbol = decider.fresh(joinFunctionName, actualResultFuncSort)
          val tActualVar = Apply(summarySymbol, joinFunctionArgs)
          val (tActualResult: Term, tAuxResult: Set[Term], cOpt) = combine(localResults, tActualVar === _)
          val c1 = cOpt.getOrElse(c)

          decider.assume(tAuxResult + tActualResult)

          val tJoined = tActualVar

          val cJoined =
            c1.copy(branchConditions = c.branchConditions,
                    additionalTriggers = if (c1.recordPossibleTriggers) tActualVar :: c1.additionalTriggers
                                         else c1.additionalTriggers)
          Q(tJoined, cJoined)
      }
    }
  }

  private case class LocalEvaluationResult(πGuards: Stack[Term],
                                           actualResult: Term,
                                           auxiliaryTerms: Set[Term],
                                           context: C)

  private def combine(localResults: Seq[LocalEvaluationResult],
                      actualResultTransformer: Term => Term = Predef.identity)
                     : (Term, Set[Term], Option[C]) = {

    val (t1: Term, tAux: Set[Term], optC) =
      localResults.map { lr =>
        val newGuards = lr.πGuards filterNot decider.π.contains
        val guard: Term = And(newGuards)
        val tAct: Term = Implies(guard, actualResultTransformer(lr.actualResult))
        val tAux: Term = Implies(guard, And(lr.auxiliaryTerms))

        (tAct, tAux, lr.context)
      }.foldLeft((True(): Term, Set[Term](), None: Option[C])) {
        case ((tActAcc, tAuxAcc, optCAcc), (tAct, _tAux, _c)) =>
          val cAcc = optCAcc.fold(_c)(cAcc => cAcc.merge(_c))

          (And(tActAcc, tAct), tAuxAcc + _tAux, Some(cAcc))
      }

    (t1, tAux, optC)
  }
}
