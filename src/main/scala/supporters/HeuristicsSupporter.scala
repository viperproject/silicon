package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.errors.Internal
import silver.verifier.reasons.{InsufficientPermission, MagicWandChunkNotFound}
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
            with Executor[ST, H, S, DefaultContext[H]]
            with MagicWandSupporter[ST, H, PC, S] =>

//  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]
//  import decider.fresh
//
//  protected val stateFactory: StateFactory[ST, H, S]
//  import stateFactory._

  protected val config: Config

  object heuristicsSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

//    private type I = (S, H, C)
//      /* TODO: We probably cannot really be generic because reactions simply
//       *       require certain inputs (and return certain outputs)
//       */

    @inline
    def tryOperation//[I, O]
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (H, Term, List[CH], C) => VerificationResult) => VerificationResult)
                    (Q: (H, Term, List[CH], C) => VerificationResult)
                    : VerificationResult = {

      tryWithReactions(σ, h, c)(action, None, 1)(Q)
    }

    def tryWithReactions//[I, O]
                        (σ: S, h: H, c: C)
                        (action: (S, H, C, (H, Term, List[CH], C) => VerificationResult) => VerificationResult,
                         initialFailure: Option[Failure[ST, H, S]]/*,
                         reactions: Seq[I => (I => VerificationResult) => VerificationResult]*/,
                         depth: Int)
                        (Q: (H, Term, List[CH], C) => VerificationResult)
                        : VerificationResult = {

//      var currentInput = input
//      var remainingReactions = heuristics
//      var initialActionFailure: Option[Failure[ST, H, S]] = None
//      var actionFailure: Option[Failure[ST, H, S]] = None
//      var globalActionResult: VerificationResult = Success()
      var localActionSuccess = false
//      var continue = false

      println(s"\n[tryWithReactions] depth = $depth")
//      println(s"  s.h = ${σ.h.values}")
//      println(s"  h = ${h.values}")
//      println(s"  c.reserveHeaps = ${c.reserveHeaps}")
//      println(s"  c.exhaleExt = ${c.exhaleExt}")

//      do {
      val globalActionResult =
        action(σ, h, c, (h1, snap, chs, c1) => {
          println(s"  action succeeded locally")
//            println(s"\n  s = $σ")
//          println(s"  h1 = ${h1.values}")
//          println(s"  chs = $chs")
//          println(s"  c1.reserveHeaps = ${c1.reserveHeaps}")
//          println(s"  c1.exhaleExt = ${c1.exhaleExt}")
          localActionSuccess = true
          Q(h1, snap, chs, c1)})

//      println(s"\n  globalActionResult (at depth $depth) = $globalActionResult")
//          println(s"  localActionSuccess = $localActionSuccess")
//          println(s"  initialActionFailure = $initialActionFailure\n")

      var reactionResult: VerificationResult = globalActionResult
        /* A bit hacky, but having an initial result here simplifies things quite a bit */

        globalActionResult match {
          case _ if localActionSuccess || globalActionResult == Success() =>
            return globalActionResult

          case actionFailure: Failure[ST, H, S] =>
            if (   c.program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))
                && depth <= config.maxHeuristicsDepth()) {

              var remainingReactions = generateReactions(σ, h, c, actionFailure)
              var triedReactions = 0

              while (reactionResult != Success() && remainingReactions.nonEmpty) {
                println(s"  trying next reaction (${triedReactions + 1} out of ${triedReactions + remainingReactions.length}})")

                reactionResult = remainingReactions.head.apply(σ, h, c)((σ1, h1, c1) =>
                  tryWithReactions(σ1, h1, c1)(action, initialFailure.orElse(Some(actionFailure)), depth + 1)(Q))

                println(s"  returned from reaction ${triedReactions + 1} (out of ${triedReactions + remainingReactions.length}})")
                //              println(s"    reactionResult = $reactionResult")

                triedReactions += 1

                //              reactionResult match {
                //                case Success() =>
                //                  return reactionResult
                //
                //                case reactionFailure: Failure[ST, H, S] =>
                remainingReactions = remainingReactions.tail
                //              }
              }
            }
        }

        reactionResult match {
          case Success() =>
            reactionResult

          case reactionFailure: Failure[ST, H, S] =>
            initialFailure.getOrElse(globalActionResult)
        }

//      } while (continue)
//
//      println(s"  tryWithHeuristic finished with global action result $globalActionResult")
////      println(s"initialActionFailure = $initialActionFailure")
//
//      if (globalActionResult.isFatal) {
//        initialActionFailure.getOrElse(globalActionResult)
//      } else
//        globalActionResult
    }

//    def generateReactions[I](input: I, cause: Failure[ST, H, S]): Seq[I => Either[Failure[ST, H, S], I]] = {
    def generateReactions/*[I]*/
                         (σ: S, h: H, c: C, cause: Failure[ST, H, S])
                         : Seq[(S, H, C) => ((S, H, C) => VerificationResult) => VerificationResult] = {

      /* HS1: Apply/unfold if wand/pred containing missing wand or acc
       * HS2: package/fold missing wand/pred
       * HS3: Apply/unfold all other wands/preds
       */

      val pve = Internal(ast.True()())

      cause.message.reason match {
        case reason: MagicWandChunkNotFound =>
          /* HS1 (wands) */
          val wand = reason.offendingNode
          val structureMatcher = heuristicsSupporter.matchers.structure(wand, c.program)
          val wands = heuristicsSupporter.wandInstancesMatching(σ, h, c, structureMatcher)
          val applyWandReactions = wands map (wand => heuristicsSupporter.applyWand(wand, pve) _)

          /* HS2 */
          val packageReaction = heuristicsSupporter.packageWand(wand, pve) _

          applyWandReactions ++ Seq(packageReaction)

        case reason: InsufficientPermission =>
          /* HS1 (wands) */
          val locationMatcher = heuristicsSupporter.matchers.location(reason.offendingNode.loc(c.program), c.program)
          val wands = heuristicsSupporter.wandInstancesMatching(σ, h, c, locationMatcher)
          val applyWandReactions = wands map (wand => heuristicsSupporter.applyWand(wand, pve) _)

          applyWandReactions

        case _ => Nil
      }
    }

//    /* Type-specific instances of tryWithHeuristic */
//
//    def tryOperation(σ: S, h: H, c: C)
//                    (action: (S, H, C, (H, Term, List[CH], C) => VerificationResult) => VerificationResult)
//                    (Q: (H, Term, List[CH], C) => VerificationResult) = (
//
//      tryOperation[(S, H, C), (H, Term, List[CH], C)]
//                  ((σ, h, c), c.program)
//                  (action = triple => QS => action(triple._1, triple._2, triple._3,  scala.Function.untupled(QS)))
//                  (Q.tupled)
//    )

    /* Heuristics */

    def packageWand(wand: ast.MagicWand, pve: PartialVerificationError)
                   (σ: S, h: H, c: C)
                   (Q: (S, H, C) => VerificationResult)
                   : VerificationResult = {

      val p = FullPerm()
//      var inputAfterHeuristic: Option[(S, H, C)] = None
//
//      val r =
        if (c.exhaleExt) {
          println(s"  reaction: packaging $wand")
          val packagingExp = ast.Packaging(wand, ast.True()())()
          consume(σ \ h, p, packagingExp, pve, c)((σ2, _, _, c2) => {
//            inputAfterHeuristic = Some((σ2, σ2.h, c2))
//            Success()})
            Q(σ2, σ2.h, c2)})
        } else {
          println(s"  reaction: package $wand")
          val packageStmt = ast.Package(wand)()
          exec(σ \ h, packageStmt, c)((σ1, c1) => {
            Q(σ1, σ1.h, c1)})
//            inputAfterHeuristic = Some((σ1, σ1.h, c1))
//            Success()})
        }

//      assert(!(r == Success() && inputAfterHeuristic == None))
//
//      //              println(s"  heuristic has been applied")
//      //              println(s"    result = $r")
//      //              println(s"    inputAfterHeuristic = $inputAfterHeuristic")
//      inputAfterHeuristic match {
//        case Some(newInput) => Right(newInput)
//        case None => Left(r.asInstanceOf[Failure[ST, H, S]])
//      }
    }

    def applyWand(wand: ast.MagicWand, pve: PartialVerificationError)
                 (σ: S, h: H, c: C)
                 (Q: (S, H, C) => VerificationResult)
                 : VerificationResult = {
//                 : Either[Failure[ST, H, S], (S, H, C)] = {

      val p = FullPerm()
//      var inputAfterHeuristic: Option[(S, H, C)] = None
//
//      val r =
        if (c.exhaleExt) {
          println(s"  reaction: applying $wand")
          val lhsAndWand = ast.And(wand.left, wand)()
          magicWandSupporter.applyingWand(σ \ h, wand, lhsAndWand, pve, c)(Q)
//          val applyingExp = ast.Applying(wand, ast.True()())()
//          consume(σ \ h, p, applyingExp, pve, c)((σ2, _, _, c2) => {
//            println(s"  finished consuming $applyingExp")
//            println(s"  s2.h = ${σ2.h}")
//            println(s"  s2.reserveHeaps = ${c2.reserveHeaps}")
//            println(s"  c2.exhaleExt = ${c2.exhaleExt}")
////            inputAfterHeuristic = Some((σ2, σ2.h, c2))
////            Success()})
//              Q(σ2, σ2.h, c2)})
        } else {
          println(s"  reaction: apply $wand")
          val applyStmt = ast.Apply(wand)()
          exec(σ \ h, applyStmt, c)((σ1, c1) => {
//            inputAfterHeuristic = Some((σ1, σ1.h, c1))
//            Success()})
            Q(σ1, σ1.h, c1)})
        }

//      assert(!(r == Success() && inputAfterHeuristic == None))
//
////      println(s"  heuristic has been applied")
////      println(s"    result = $r")
////      println(s"    inputAfterHeuristic = $inputAfterHeuristic")
//      inputAfterHeuristic match {
//        case Some(newInput) => Right(newInput)
//        case None => Left(r.asInstanceOf[Failure[ST, H, S]])
//      }
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

//    def wandInstancesMentioningLocation(σ: S, h: H, location: ast.Location, c: C): Seq[ast.MagicWand] = {

    def wandInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[silver.ast.Node, _]): Seq[ast.MagicWand] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val wands = allChunks.collect {
        case ch: MagicWandChunk =>
          ch.ghostFreeWand.right.existsDefined(f)/* {
            case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(c.program) == location =>
          }*/ match {
            case true => Some(ch.ghostFreeWand)
            case _ => None
          }
      }.flatten.toSeq

      println("[wandInstancesMentioningLocation]")
      println(s"  wands = $wands")

      wands
    }

    object matchers {
      def location(loc: ast.Location, program: ast.Program): PartialFunction[silver.ast.Node, Any] = {
        case ast.AccessPredicate(locacc: ast.LocationAccess, _) if locacc.loc(program) == loc =>
      }

      def structure(wand: ast.MagicWand, program: ast.Program): PartialFunction[silver.ast.Node, Any] = {
        case other: ast.MagicWand if wand.structurallyMatches(other, program) =>
      }
    }
  }
}
