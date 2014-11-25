package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import interfaces.{Evaluator, Producer, Consumer, Executor, VerificationResult, Failure, Success}
import interfaces.state.{/*StateFactory,*/ Chunk, State, PathConditions, Heap, Store}
import state.{MagicWandChunk, DirectPredicateChunk, DefaultContext}
import state.terms._

trait HeuristicsSupporter[ST <: Store[ST],
                        H <: Heap[H],
                        PC <: PathConditions[PC],
                        S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[Chunk, ST, H, S, DefaultContext[H]]
            with Executor[ST, H, S, DefaultContext[H]] =>

//  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]
//  import decider.fresh
//
//  protected val stateFactory: StateFactory[ST, H, S]
//  import stateFactory._

  object heuristicsSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

    def tryWithHeuristic[I, O]
                        (c: C, input: I)
                        (action: I => (O => VerificationResult) /*=> (Failure[ST, H, S] => VerificationResult)*/ => VerificationResult,
                         heuristics: Seq[I => Either[Failure[ST, H, S], I]])
                        (Q: O => VerificationResult)
                        : VerificationResult = {

      var currentInput = input
      var remainingReactions = heuristics
      var initialActionFailure: Option[Failure[ST, H, S]] = None
      var actionFailure: Option[Failure[ST, H, S]] = None
      var globalActionResult: VerificationResult = Success()
      var actionLocallySucceeded = false
      var continueApplyingHeuristics = false

      println(s"\n[tryWithHeuristic]")

      do {
        println(s"\n  current input = $currentInput")

        globalActionResult = (
          action(currentInput)
                (output => {
                  println(s"  action succeeded locally")
                  actionLocallySucceeded = true
                  Q(output)
                }))

        println(s"\n  globalActionResult = $globalActionResult")
        println(s"  actionLocallySucceeded = $actionLocallySucceeded")
        println(s"  initialActionFailure = $initialActionFailure\n")

        globalActionResult match {
          case _: Success => continueApplyingHeuristics = false
          case _ if actionLocallySucceeded => continueApplyingHeuristics = false

          case failure: Failure[ST, H, S] =>
            if (initialActionFailure.isEmpty)
              initialActionFailure = Some(failure)

            var heuristicResult: Either[Failure[ST, H, S], I] = Left(null)

            while (   heuristicResult.isLeft
                   && remainingReactions.nonEmpty
                   && c.program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))) {

              println(s"  applying next heuristic")
              heuristicResult = remainingReactions.head.apply(input)
              println(s"  heuristic globalActionResult: ${heuristicResult.getClass.getSimpleName}")

              remainingReactions = remainingReactions.tail
            }

            heuristicResult match {
              case Left(_) =>
                continueApplyingHeuristics = false

              case Right(newInput) =>
                currentInput = newInput
                continueApplyingHeuristics = true
            }
        }
      } while (continueApplyingHeuristics)

      println(s"  tryWithHeuristic finished with global action result $globalActionResult")
//      println(s"initialActionFailure = $initialActionFailure")

      if (globalActionResult.isFatal) {
        initialActionFailure.getOrElse(globalActionResult)
      } else
        globalActionResult
    }

    /* Type-specific instances of tryWithHeuristic */

    def tryWithHeuristic(σ: S, h: H, c: C)
                        (action: (S, H, C, (H, Term, List[CH], C) => VerificationResult) => VerificationResult,
                         heuristics: Seq[(S, H, C) => Either[Failure[ST, H, S], (S, H, C)]])
                        (Q: (H, Term, List[CH], C) => VerificationResult) =

      tryWithHeuristic[(S, H, C), (H, Term, List[CH], C)](c, (σ, h, c))(
        action = triple => QS => action(triple._1, triple._2, triple._3,  scala.Function.untupled(QS)),
        heuristics = heuristics.map(_.tupled)
      )(Q.tupled)

    /* Heuristics */

    def packageWand(wand: ast.MagicWand, pve: PartialVerificationError)
                   (σ: S, h: H, c: C)
                   : Either[Failure[ST, H, S], (S, H, C)] = {

      val p = FullPerm()
      var inputAfterHeuristic: Option[(S, H, C)] = None

      val r =
        if (c.exhaleExt) {
          println(s"  heuristic: packaging $wand")
          val packagingExp = ast.Packaging(wand, ast.True()())()
          consume(σ \ h, p, packagingExp, pve, c)((σ2, _, _, c2) => {
            inputAfterHeuristic = Some((σ2, σ2.h, c2))
            Success()})
        } else {
          println(s"  heuristic: package $wand")
          val packageStmt = ast.Package(wand)()
          exec(σ \ h, packageStmt, c)((σ1, c1) => {
            inputAfterHeuristic = Some((σ1, σ1.h, c1))
            Success()})
        }

      assert(!(r == Success() && inputAfterHeuristic == None))

      //              println(s"  heuristic has been applied")
      //              println(s"    result = $r")
      //              println(s"    inputAfterHeuristic = $inputAfterHeuristic")
      inputAfterHeuristic match {
        case Some(newInput) => Right(newInput)
        case None => Left(r.asInstanceOf[Failure[ST, H, S]])
      }
    }

    def applyWand(wand: ast.MagicWand, pve: PartialVerificationError)
                 (σ: S, h: H, c: C)
                 : Either[Failure[ST, H, S], (S, H, C)] = {

      val p = FullPerm()
      var inputAfterHeuristic: Option[(S, H, C)] = None

      val r =
        if (c.exhaleExt) {
          println(s"  heuristic: applying $wand")
          val applyingExp = ast.Applying(wand, ast.True()())()
          consume(σ \ h, p, applyingExp, pve, c)((σ2, _, _, c2) => {
            println(s"  finished consuming $applyingExp")
            println(s"  s2.h = ${σ2.h}")
            println(s"  s2.reserveHeaps = ${c2.reserveHeaps}")
            inputAfterHeuristic = Some((σ2, σ2.h, c2))
            Success()})
        } else {
          println(s"  heuristic: apply $wand")
          val applyStmt = ast.Apply(wand)()
          exec(σ \ h, applyStmt, c)((σ1, c1) => {
            inputAfterHeuristic = Some((σ1, σ1.h, c1))
            Success()})
        }

      assert(!(r == Success() && inputAfterHeuristic == None))

//      println(s"  heuristic has been applied")
//      println(s"    result = $r")
//      println(s"    inputAfterHeuristic = $inputAfterHeuristic")
      inputAfterHeuristic match {
        case Some(newInput) => Right(newInput)
        case None => Left(r.asInstanceOf[Failure[ST, H, S]])
      }
    }

    /* Helpers */

    def predicateInstancesMentioningLocation(σ: S, h: H, location: ast.Location, c: C): Seq[ast.PredicateAccessPredicate] = {
      val predicateChunks =
        h.values.collect {
          case ch: DirectPredicateChunk =>
            val body = c.program.findPredicate(ch.name)

            body.existsDefined {
              case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(c.program) == location =>
            } match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten


      val predicateAccesses =
        predicateChunks.map {
          case DirectPredicateChunk(name, args, _, _, _) =>
            val reversedArgs: Seq[ast.Expression] =
              args map {
                case True() => ast.True()()
                case False() => ast.False()()
                case IntLiteral(n) => ast.IntegerLiteral(n)()
                case t => σ.γ.values.find(p => p._2 == t).get._1
              }

            ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, c.program.findPredicate(name))(), ast.FullPerm()())()
        }.toSeq

      println("[predicateInstancesMentioningLocation]")
      println(s"  predicateAccesses = $predicateAccesses")

      predicateAccesses
    }

    def wandInstancesMentioningLocation(σ: S, h: H, location: ast.Location, c: C): Seq[ast.MagicWand] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val wands = allChunks.collect {
        case ch: MagicWandChunk =>
          ch.ghostFreeWand.existsDefined {
            case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(c.program) == location =>
          } match {
            case true => Some(ch.ghostFreeWand)
            case _ => None
          }
      }.flatten.toSeq

      println("[wandInstancesMentioningLocation]")
      println(s"  wands = $wands")

      wands
    }
  }
}
