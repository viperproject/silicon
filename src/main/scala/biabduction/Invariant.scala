package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, VerificationResult}
import viper.silicon.rules.{executor, producer}
import viper.silicon.state.State
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Exp, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

case class InvariantAbductionQuestion(abstractions: Seq[Seq[Exp]], assignments: Seq[Exp], nextState: Seq[Exp])

object LoopInvariantSolver {
  val pve: PartialVerificationError = Internal()

  def solve(s: State,
            v: Verifier,
            loopEdges: Seq[Edge[Stmt, Exp]],
            joinPoint: Option[SilverBlock],
            q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Seq(), Seq()))
           (Q: AbductionResult => VerificationResult): VerificationResult = {

    // Assumme that we have the things in nextState
    producer.produces(s, freshSnap, q.nextState, _ => pve, v) { (s2, v2) =>

      // Run the loop
      // This continuation should never be called, we are only following the inner loop edges, which either
      // fails, or returns a Success with the found postconditions. So the match below should always succeed.
      val res = executor.follows(s2, loopEdges, _ => pve, v2, joinPoint)((_, _) => Success())

      res match {
        // If we find a new precondition, add it to next state and restart
        case f@Failure(res, _) =>
          res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
            case Some(a: AbductionSuccess) =>
              val newState = q.nextState ++ a.pre
              solve(s, v, loopEdges, joinPoint, q.copy(nextState = newState))(Q)
            case _ => Q(AbductionFailure())
          }

        // We successfully reached the end of the loop, so we can proceed
        case Success(Some(a)) =>

          // Perform abstraction on the found state for that loop iteration
          val prevAbst = q.abstractions.lastOption match {
            case Some(abst) => abst
            case _ => Seq()
          }
          val nextAbst = AbstractionApplier.apply(AbstractionQuestion(prevAbst ++ q.nextState, s.program)).exps
          // Check if we are done
          // TODO finish
          Q(AbductionFailure())

      }
    }
  }
}


// TODO stop ignoring this case
// We reached the end of the loop and found posts that we want to add to the invariant
//case Success(Some(AbductionSuccess(post :: ps, _))) => ???
