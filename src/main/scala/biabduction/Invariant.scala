package viper.silicon.biabduction

import viper.silicon.interfaces.{Failure, SiliconFailureContext, Success, Unreachable, VerificationResult}
import viper.silicon.rules.{executor, producer}
import viper.silicon.state.State
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Exp, LocalVar, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.Internal

// abstractions contains the abstractions after each loop iteration
// assignments contains the value (as an expression at the beginning of the loop!) of the iterated variables after each loop iteration
// nextState contains the things we abduce during the current iteration
case class InvariantAbductionQuestion(abstractions: Seq[Seq[Exp]], assignments: Map[LocalVar, Exp], nextState: Seq[Exp])

object LoopInvariantSolver {
  val pve: PartialVerificationError = Internal()

  def solve(s: State,
            v: Verifier,
            loopEdges: Seq[Edge[Stmt, Exp]],
            joinPoint: Option[SilverBlock],
            q: InvariantAbductionQuestion = InvariantAbductionQuestion(Seq(), Map(), Seq()))
           (Q: AbductionResult => VerificationResult): VerificationResult = {

    def pveLam(a: Exp) = pve

    // Assumme that we have the things in nextState
    producer.produces(s, freshSnap, q.nextState, pveLam, v) { (s2, v2) =>

      // Run the loop
      // This continuation should never be called, we are only following the inner loop edges, which either
      // fails, or returns a Success with the found postconditions. So the match below should always succeed.
      val res = executor.follows(s2, loopEdges, pveLam, v2, joinPoint)((_, _) => Success())

      res match {
        // If we find a new precondition, add it to next state and restart
        case Failure(res, _) =>
          res.failureContexts.head.asInstanceOf[SiliconFailureContext].abductionResult match {
            case Some(a: AbductionSuccess) =>
              val newState = q.nextState ++ a.pre
              solve(s, v, loopEdges, joinPoint, q.copy(nextState = newState))(Q)
            case _ => Q(AbductionFailure(s2, v2))
          }

        // We successfully reached the end of the loop, so we can proceed
        // Loop bodies are executed using branching with a meaningless else branch. This else branch returns Unreachable
        // and the result we are actually interested in is in the previous field of this Unreachable.
        // This is brittle and terrifying, a constant reminder of the horrors of the reality.
        case Unreachable() =>

          res.previous.head match {
            case Success(Some(a: AbductionSuccess)) =>

              // Find the new assignments
              // Idea for now: take all variables in store that have changed and can be reduced to beginning
              // TODO

              // Perform abstraction on the found state for that loop iteration
              val prevAbst = q.abstractions.lastOption match {
                case Some(abst) => abst
                case _ => Seq()
              }
              val nextAbst = AbstractionApplier.apply(AbstractionQuestion(prevAbst ++ q.nextState, s.program)).exps

              // Check if we are done
              // This means that the abstraction is the same if we replace via the found assignment
              // Then we want to find the actual invariants!
              // TODO

              // Else continue with next iteration, using the state from the end of the loop
              solve(a.s, a.v, loopEdges, joinPoint, q.copy(abstractions = q.abstractions :+ nextAbst, nextState = Seq()))(Q)
          }
      }
    }
  }
}


// TODO stop ignoring this case
// We reached the end of the loop and found posts that we want to add to the invariant
//case Success(Some(AbductionSuccess(post :: ps, _))) => ???
