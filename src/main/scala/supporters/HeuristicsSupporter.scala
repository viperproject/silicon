package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.InsufficientPermission
import viper.silicon.interfaces._
import interfaces.decider.Decider
import interfaces.state.{StateFactory, Chunk, ChunkIdentifier, State, PathConditions, Heap, Store}
import interfaces.state.factoryUtils.Ø
import viper.silicon.state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk, MagicWandChunk}
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNoAccess, IsAsPermissive}

trait HeuristicsSupporter[ST <: Store[ST],
                        H <: Heap[H],
                        PC <: PathConditions[PC],
                        S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[Chunk, ST, H, S, DefaultContext[H]] =>

  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]
  import decider.fresh

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  object heuristicsSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

    def tryWithHeuristic(σ: S, h: H, c: C)
                        (action: (S, H, C, (H, Term, List[CH], C) => VerificationResult, Failure[ST, H, S] => VerificationResult) => VerificationResult,
                         heuristics: Seq[(S, H, C) => Either[Failure[ST, H, S], (S, H, C)]])
                        (Q: (H, Term, List[CH], C) => VerificationResult) =

      tryWithHeuristic[(S, H, C), (H, Term, List[CH], C)](c, (σ, h, c))(
        action = triple => QS => QF => action(triple._1, triple._2, triple._3,  scala.Function.untupled(QS), QF),
        heuristics = heuristics.map(_.tupled)
      )(Q.tupled)

    def tryWithHeuristic[I, O]
                        (c: C, input: I)
                        (action: I => (O => VerificationResult) => (Failure[ST, H, S] => VerificationResult) => VerificationResult,
                         heuristics: Seq[I => Either[Failure[ST, H, S], I]])
                        (Q: O => VerificationResult)
                        : VerificationResult = {

      var currentInput = input
      var remainingReactions = heuristics
      var initialActionFailure: Option[Failure[ST, H, S]] = None
      var actionFailure: Option[Failure[ST, H, S]] = None
      var actionResult: VerificationResult = Success()
      var continue = false

      println(s"\n[tryWithHeuristic]")

      do {
        //        println(s"\n  current input = $currentInput")

        actionResult = (
          action(currentInput)
                (output => {
                  println(s"  action succeeded")
                  actionFailure = None
                  Q(output)
                })
                (failure => {
                  println(s"  action failed: $failure")
                  actionFailure = Some(failure)
                  failure
                }))

        //        println(s"\n  actionResult = $actionResult")
        //        println(s"\n  actionFailure = $actionFailure")
        //        println(s"\n  initialActionFailure = $initialActionFailure")

        //        continue = actionFailure.nonEmpty && remainingReactions.nonEmpty

        actionFailure match {
          case None =>
            continue = false

          case Some(_) =>
            if (initialActionFailure.isEmpty)
              initialActionFailure = actionFailure

            var heuristicResult: Either[Failure[ST, H, S], I] = Left(null)

            while (   heuristicResult.isLeft
              && remainingReactions.nonEmpty
              && c.program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))) {

              println(s"  applying next heuristic")
              heuristicResult = remainingReactions.head.apply(input)
              println(s"  heuristic actionResult: ${heuristicResult.getClass.getSimpleName}")

              remainingReactions = remainingReactions.tail
            }

            heuristicResult match {
              case Left(_) =>
                continue = false

              case Right(newInput) =>
                currentInput = newInput
                continue = true
            }
        }
      } while (continue)

      println(s"  tryWithHeuristic finished: $actionResult")

      if (actionResult.isFatal) {
        initialActionFailure.getOrElse(actionResult)
      } else
        actionResult
    }
  }
}
