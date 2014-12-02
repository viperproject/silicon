package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.errors.{HeuristicsFailed, Internal}
import silver.verifier.reasons.{InternalReason, InsufficientPermission, MagicWandChunkNotFound}
import interfaces.{Evaluator, Producer, Consumer, Executor, VerificationResult, Failure, Success}
import interfaces.state.{Chunk, State, PathConditions, Heap, Store, FieldChunk}
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

  protected val config: Config

  object heuristicsSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

    @inline
    def tryOperation[O1, O2]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2), C) => VerificationResult) =>
        action(σ1, h1, c1, (o1: O1, o2: O2, c2) => QS((o1, o2), c2))

      val tupledQ = (os: (O1, O2), c1: C) => Q(os._1, os._2, c1)

      tryWithReactions[(O1, O2)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    @inline
    def tryOperation[O1, O2, O3]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, O3, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, O3, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2, O3), C) => VerificationResult) =>
          action(σ1, h1, c1, (o1: O1, o2: O2, o3: O3, c2) => QS((o1, o2, o3), c2))

      val tupledQ = (os: (O1, O2, O3), c1: C) => Q(os._1, os._2, os._3, c1)

      tryWithReactions[(O1, O2, O3)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    @inline
    def tryOperation[O1, O2, O3, O4]
                    (description: String)
                    (σ: S, h: H, c: C)
                    (action: (S, H, C, (O1, O2, O3, O4, C) => VerificationResult) => VerificationResult)
                    (Q: (O1, O2, O3, O4, C) => VerificationResult)
                    : VerificationResult = {

      val tupledAction = (σ1: S, h1: H, c1: C, QS: ((O1, O2, O3, O4), C) => VerificationResult) =>
        action(σ1, h1, c1, (o1: O1, o2: O2, o3: O3, o4: O4, c2) => QS((o1, o2, o3, o4), c2))

      val tupledQ = (os: (O1, O2, O3, O4), c1: C) => Q(os._1, os._2, os._3, os._4, c1)

      tryWithReactions[(O1, O2, O3, O4)](description)(σ, h, c)(tupledAction, None)(tupledQ)
    }

    private def tryWithReactions[O]
                                (description: String)
                                (σ: S, h: H, _c: C)
                                (action: (S, H, C, (O, C) => VerificationResult) => VerificationResult,
                                 initialFailure: Option[Failure[ST, H, S]])
                                (Q: (O, C) => VerificationResult)
                                : VerificationResult = {

      val c = _c
//        if (_c.heuristicsDepth < config.maxHeuristicsDepth())
//          _c.copy(heuristicsDepth = _c.heuristicsDepth + 1)
//        else
//          _c.copy(applyHeuristics = false)

      var localActionSuccess = false

      println(s"\n[tryWithReactions]")
      println(s" depth = ${c.heuristicsDepth}")
      println(s" applyHeuristics = ${c.applyHeuristics}")
      println(s" description = $description")
//      Thread.sleep(500)

      val globalActionResult =
        action(σ, h, c, (outputs, c1) => {
          println(s"  action succeeded locally")
          localActionSuccess = true
          val c2 = c1.copy(/*applyHeuristics = _c.applyHeuristics,*/ heuristicsDepth = 0)
          Q(outputs, c2)})

      println(s"  globalActionResult (${c.heuristicsDepth}, $description) = $globalActionResult")
//      println(s"  localActionSuccess = $localActionSuccess")

      var reactionResult: VerificationResult = globalActionResult
        /* A bit hacky, but having an initial result here simplifies things quite a bit */

        globalActionResult match {
          case _ if localActionSuccess || !globalActionResult.isFatal =>
            return globalActionResult

          case actionFailure: Failure[ST, H, S] =>
            if (c.applyHeuristics && c.heuristicsDepth <= config.maxHeuristicsDepth()) {
              var remainingReactions = generateReactions(σ, h, c, actionFailure)
              var triedReactions = 0

              while (reactionResult != Success() && remainingReactions.nonEmpty) {
                println(s"  trying next reaction (${triedReactions + 1} out of ${triedReactions + remainingReactions.length}})")

                val c1 = c.copy(heuristicsDepth = c.heuristicsDepth + 1)
                reactionResult = remainingReactions.head.apply(σ, h, c1)((σ1, h1, c2) => {
                  tryWithReactions(description)(σ1, h1, c2)(action, initialFailure.orElse(Some(actionFailure)))(Q)})

                println(s"  returned from reaction ${triedReactions + 1} (out of ${triedReactions + remainingReactions.length}})")

                triedReactions += 1

                remainingReactions = remainingReactions.tail
              }
            }
        }

        reactionResult match {
          case _ if !reactionResult.isFatal =>
            reactionResult

          case reactionFailure: Failure[ST, H, S] =>
            initialFailure.getOrElse(globalActionResult)
        }
    }

    def generateReactions(σ: S, h: H, c: C, cause: Failure[ST, H, S])
                         : Seq[(S, H, C) => ((S, H, C) => VerificationResult) => VerificationResult] = {

      /* HS1: Apply/unfold if wand/pred containing missing wand or acc
       * HS2: package/fold missing wand/pred
       * HS3: Apply/unfold all other wands/preds
       */

      val pve = HeuristicsFailed(ast.True()()) /* TODO: Use a meaningful node */

      cause.message.reason match {
        case reason: MagicWandChunkNotFound =>
          /* HS1 (wands) */
          val wand = reason.offendingNode
          val structureMatcher = matchers.structure(wand, c.program)
          val wands = wandInstancesMatching(σ, h, c, structureMatcher)
          val applyWandReactions = wands map (wand => applyWand(wand, pve) _)

          /* HS2 */
          val packageReaction = packageWand(wand, pve) _

          applyWandReactions /*++ Seq(packageReaction)*/

        case reason: InsufficientPermission =>
          val locationMatcher = matchers.location(reason.offendingNode.loc(c.program), c.program)

          /* HS1 (wands) */
          val wands = wandInstancesMatching(σ, h, c, locationMatcher)
          val applyWandReactions = wands map (wand => applyWand(wand, pve) _)

          /* HS1 (predicates) */
          val predicates = predicateInstancesMatching(σ, h, c, locationMatcher)
          val unfoldPredicateReactions = predicates map (predicate => unfoldPredicate(predicate, pve) _)

          /* HS2 (predicates) */
          val foldPredicateReaction =
            reason.offendingNode match {
              case pa: ast.PredicateAccess =>
                val acc = ast.PredicateAccessPredicate(pa, ast.FullPerm()())()
                Some(foldPredicate(acc, pve) _)

              case _ => None
            }

          applyWandReactions /*++ unfoldPredicateReactions ++ foldPredicateReaction.toSeq*/

        case _ => Nil
      }
    }

    /* Heuristics */

    def packageWand(wand: ast.MagicWand, pve: PartialVerificationError)
                   (σ: S, h: H, c: C)
                   (Q: (S, H, C) => VerificationResult)
                   : VerificationResult = {

      val p = FullPerm()

      if (c.exhaleExt) {
        println(s"  reaction: packaging $wand")
        val packagingExp = ast.Packaging(wand, ast.True()())()
        consume(σ \ h, p, packagingExp, pve, c)((σ2, _, _, c2) => {
          Q(σ2, σ2.h, c2)})
      } else {
        println(s"  reaction: package $wand")
        val packageStmt = ast.Package(wand)()
        exec(σ \ h, packageStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def applyWand(wand: ast.MagicWand, pve: PartialVerificationError)
                 (σ: S, h: H, c: C)
                 (Q: (S, H, C) => VerificationResult)
                 : VerificationResult = {

      /* TODO: Test combination of applyWand-heuristic and wand references (wand w := ...) */

      if (c.exhaleExt) {
        println(s"  reaction: applying $wand")
        val lhsAndWand = ast.And(wand.left, wand)()
        magicWandSupporter.applyingWand(σ \ h, σ.γ, wand, lhsAndWand, pve, c)(Q)
      } else {
        println(s"  reaction: apply $wand")
        val applyStmt = ast.Apply(wand)()
        exec(σ \ h, applyStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def unfoldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                       (σ: S, h: H, c: C)
                       (Q: (S, H, C) => VerificationResult)
                       : VerificationResult = {


      if (c.exhaleExt) {
        println(s"  reaction: unfolding $acc")
        magicWandSupporter.unfoldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        println(s"  reaction: unfold $acc")
        val unfoldStmt = ast.Unfold(acc)()
        exec(σ \ h, unfoldStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

    def foldPredicate(acc: ast.PredicateAccessPredicate, pve: PartialVerificationError)
                     (σ: S, h: H, c: C)
                     (Q: (S, H, C) => VerificationResult)
                     : VerificationResult = {

      if (c.exhaleExt) {
        println(s"  reaction: folding $acc")
        magicWandSupporter.foldingPredicate(σ \ h, acc, pve, c)(Q)
      } else {
        println(s"  reaction: fold $acc")
        val foldStmt = ast.Fold(acc)()
        exec(σ \ h, foldStmt, c)((σ1, c1) => {
          Q(σ1, σ1.h, c1)})
      }
    }

      /* Helpers */

    def predicateInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[silver.ast.Node, _]): Seq[ast.PredicateAccessPredicate] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val predicateChunks =
        allChunks.collect {
          case ch: DirectPredicateChunk =>
            val body = c.program.findPredicate(ch.name)

            body.existsDefined(f) match {
              case true => Some(ch)
              case _ => None
            }
        }.flatten


      val predicateAccesses =
        predicateChunks.flatMap {
          case DirectPredicateChunk(name, args, _, _, _) =>
            var success = true

            val reversedArgs: Seq[ast.Expression] =
              args map {
                case True() => ast.True()()
                case False() => ast.False()()
                case IntLiteral(n) => ast.IntegerLiteral(n)()
                case t =>
                  σ.γ.values.find(p => p._2 == t).map(_._1)
                      /* Found a local variable v s.t. v |-> t */
                    .orElse(
                      allChunks.collectFirst {
                        case fc: FieldChunk if fc.value == t =>
                          σ.γ.values.find(p => p._2 == fc.args(0))
                                    .map(_._1)
                                    .map(v => ast.FieldAccess(v, c.program.findField(fc.name))())
                      }.flatten
                        /* Found a local variable v and a field f s.t. v.f |-> t */
                    ).getOrElse {
                      success = false
                      ast.True()() /* Dummy value */
                    }
              }

            if (success)
              Some(ast.PredicateAccessPredicate(ast.PredicateAccess(reversedArgs, c.program.findPredicate(name))(), ast.FullPerm()())())
            else
              None
        }.toSeq

      predicateAccesses
    }

    def wandInstancesMatching(σ: S, h: H, c: C, f: PartialFunction[silver.ast.Node, _]): Seq[ast.MagicWand] = {
      val allChunks = σ.h.values ++ h.values ++ c.reserveHeaps.flatMap(_.values)

      val wands =
        allChunks.collect {
          case ch: MagicWandChunk =>
            ch.ghostFreeWand.right.existsDefined(f) match {
              case true => Some(ch.ghostFreeWand)
              case _ => None
            }
        }.flatten.toSeq

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
