package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.InsufficientPermission
import interfaces.{Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.state.{ChunkIdentifier, State, PathConditions, Heap, Store}
import viper.silicon.state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk, MagicWandChunk}
import state.terms._
import state.terms.perms.{IsNoAccess, IsAsPermissive}

trait MagicWandSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         PC <: PathConditions[PC],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]] =>

  protected val decider: Decider[ST, H, PC, S, DefaultContext[H]]

  object magicWandSupporter {
    private type C = DefaultContext[H]

    def isDirectWand(exp: ast.Expression) = exp match {
      case wand: ast.MagicWand => true
      case v: ast.LocalVariable => v.typ == ast.types.Wand
      case _ => false
    }

    def createChunk(σ: S, wand: ast.MagicWand, pve: PartialVerificationError, c: C)
                   (Q: (MagicWandChunk, C) => VerificationResult)
                   : VerificationResult = {

      val ghostFreeWand = wand.withoutGhostOperations
      val es = ghostFreeWand.subexpressionsToEvaluate(c.program)

      evals(σ, es, pve, c)((ts, c1) =>
        Q(MagicWandChunk(ghostFreeWand, ts), c1))
    }

    /* TODO: doWithMultipleHeaps and consumeFromMultipleHeaps have a similar
     *       structure. Try to merge the two.
     */

    def doWithMultipleHeaps[R](hs: Stack[H],
                               c: C)
                              (action: (H, C) => (Option[R], H, C))
                              (Q: (Option[R], Stack[H], C) => VerificationResult)
                              : VerificationResult = {

      var result: Option[R] = None
      var heapsToVisit = hs
      var visitedHeaps: List[H] = Nil
      var cCurr = c

      while (heapsToVisit.nonEmpty && result.isEmpty) {
        val h = heapsToVisit.head
        heapsToVisit = heapsToVisit.tail

        val (result1, h1, c1) = action(h, cCurr)
        result = result1
        visitedHeaps = h1 :: visitedHeaps
        cCurr = c1
      }

      Q(result, visitedHeaps.reverse ++ heapsToVisit, cCurr)
    }

    def consumeFromMultipleHeaps(σ: S,
                                 hs: Stack[H],
                                 id: ChunkIdentifier,
                                 pLoss: Term,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C)
                                (Q: (Stack[H], List[DirectChunk], C) => VerificationResult)
                                : VerificationResult = {

      var toLose = pLoss
      var heapsToVisit = hs
      var visitedHeaps: List[H] = Nil
      var chunks: List[DirectChunk] = Nil
      var cCurr = c

  //    println("\n[consumeFromMultipleHeaps]")
  //    println(s"  toLose = $toLose")
  //    println(s"  heapsToVisit = $heapsToVisit")
  //    println(s"  visitedHeaps = $visitedHeaps")
  //    println(s"  chunks = $chunks")

      while (heapsToVisit.nonEmpty && !decider.check(σ, IsNoAccess(toLose))) {
        val h = heapsToVisit.head
        heapsToVisit = heapsToVisit.tail

  //      println(s"\n  h = $h")
        val (h1, optCh1, toLose1, c1) = consumeMaxPermissions(σ, h, id, toLose, cCurr)
  //      println(s"  h1 = $h1")
  //      println(s"  optCh1 = $optCh1")
  //      println(s"  toLose1 = $toLose1")
        visitedHeaps = h1 :: visitedHeaps
        chunks =
          optCh1 match {
            case None => chunks
  //          case Some(ch) => (ch, visitedHeaps.length  - 1) :: chunks
            case Some(ch) => ch :: chunks
          }
        toLose = toLose1
        cCurr = c1
      }

  //    println(s"\n  X toLose = $toLose")
  //    println(s"  X heapsToVisit = $heapsToVisit")
  //    println(s"  X visitedHeaps = $visitedHeaps")
  //    println(s"  X chunks = $chunks")
  //    println(s"  X done? ${decider.check(σ, IsNoAccess(toLose))}")

      if (decider.check(σ, IsNoAccess(toLose))) {
        val tEqs =
          chunks.sliding(2).map {
  //          case List((fc1: DirectFieldChunk, _), (fc2: DirectFieldChunk, _)) => fc1.value === fc2.value
            case List(fc1: DirectFieldChunk, fc2: DirectFieldChunk) => fc1.value === fc2.value
  //          case List((pc1: DirectPredicateChunk, _), (pc2: DirectPredicateChunk, _)) => pc1.snap === pc2.snap
            case List(pc1: DirectPredicateChunk, pc2: DirectPredicateChunk) => pc1.snap === pc2.snap
            case _ => True()
          }

        decider.assume(toSet(tEqs))

        Q(visitedHeaps.reverse ++ heapsToVisit, chunks.reverse, cCurr)
      } else {
        Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
      }
    }

    /* TODO: This is similar, but not as general, as the consumption algorithm
     *       implemented for supporting quantified permissions. It should be
     *       possible to unite the two.
     */
    private def consumeMaxPermissions(σ: S,
                                      h: H,
                                      id: ChunkIdentifier,
                                      pLoss: Term,
                                      c: C)
                                     : (H, Option[DirectChunk], Term, C) = {

      decider.getChunk[DirectChunk](σ, h, id, c) match {
        case result @ Some(ch) =>
          val (pLost, pKeep, pToConsume) =
            if (decider.check(σ, IsAsPermissive(ch.perm, pLoss)))
              (pLoss, PermMinus(ch.perm, pLoss), NoPerm())
            else
              (ch.perm, NoPerm(), PermMinus(pLoss, ch.perm))
  //        println("  [consumeMaxPermissions]")
  //        println(s"    ch.perm = ${ch.perm}")
  //        println(s"    pLost = $pLost")
  //        println(s"    pKeep = $pKeep")
  //        println(s"    pToConsume = $pToConsume")
          val h1 =
            if (decider.check(σ, IsNoAccess(pKeep))) h - ch
            else h - ch + (ch \ pKeep)
          val consumedChunk = ch \ pLost
          (h1, Some(consumedChunk), pToConsume, c)

        case None => (h, None, pLoss, c)
      }
    }
  }
}
