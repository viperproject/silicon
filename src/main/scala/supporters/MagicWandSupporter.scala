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

trait MagicWandSupporter[ST <: Store[ST],
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

  object magicWandSupporter {
    private type C = DefaultContext[H]
    private type CH = Chunk

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

    def packageWand(σ: S, wand: ast.MagicWand, pve: PartialVerificationError, c: C)
                   (Q: (MagicWandChunk, C) => VerificationResult)
                   : VerificationResult = {

      val σEmp = Σ(σ.γ, Ø, σ.g)
      val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
      /* decider.locally {...} will "abort" branching executions without properly
       * joining them (which we don't really know how to handle for heaps anyway).
       * I.e., if an impure conditional occurs on the right of a wand, only the
       * final heap of the second branch will be used for the rest of the
       * execution, which is unsound.
       */
      decider.locally[(MagicWandChunk, C)](QB => {
        produce(σEmp, fresh, FullPerm(), wand.left, pve, c0)((σLhs, c1) => {
          val c2 = c1.copy(reserveHeaps = c.reserveHeaps.head +: σLhs.h +: c.reserveHeaps.tail,
                           exhaleExt = true,
                           lhsHeap = Some(σLhs.h))
          val rhs = wand.right
          consume(σEmp, FullPerm(), rhs, pve, c2)((_, _, _, c3) =>
            magicWandSupporter.createChunk(σ, wand, pve, c3)(scala.Function.untupled(QB)))})
      })(Q.tupled)
    }

//    def execGhostOp(σ: S/*, h: H*/, expToConsume: ast.Expression, expToProduce: ast.Expression, pve: PartialVerificationError, c: C)
//                   (Q: (H, C) => VerificationResult)
//                   : VerificationResult = {
//
//      assert(c.exhaleExt, s"Expected c.exhaleExt to be true, but was ${c.exhaleExt}")
//
//      val σEmp = Σ(σ.γ, Ø, σ.g)
//      //        println(s"eLHSAndWand = $eLHSAndWand")
//      consume(σEmp, FullPerm(), expToConsume, pve, c)((σ1/*h1*/, _, chs1, c1) => { /* exhale_ext, h1 = σUsed' */
//        //          println(s"chs1 = $chs1")
////        assert(chs1.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
////        val ch = chs1.last.asInstanceOf[MagicWandChunk]
//        val c1a = c1.copy(reserveHeaps = Nil, exhaleExt = false)
//        consume(σ \ σ1.h/*, h1*/, FullPerm(), expToConsume, pve, c1a)((σ2/*h2*/, _, _, c2) => { /* σUsed'.apply */
////          assert(chs2.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
////          assert(ch == chs2.last.asInstanceOf[MagicWandChunk], s"Expected $chs1 == $chs2")
//          val c2a = c2.copy(lhsHeap = Some(σ1.h/*h1*/))
//          produce(σ \ σ2.h/*h2*/, decider.fresh, FullPerm(), expToProduce, pve, c2a)((σ3, c3) => { /* σ3.h = σUsed'' */
//          val topReserveHeap = c1.reserveHeaps.head + σ3.h
//            val c3a = c3.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.tail,
//              exhaleExt = c1.exhaleExt,
//              lhsHeap = c2.lhsHeap)
//            decider.prover.logComment(s"in consume/apply after producing RHS ${eWand.right}}, before consuming $eIn")
//            consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c3a)((h4, _, _, c4) =>
//              Q(h4, decider.fresh(sorts.Snap), Nil, c4))})})})
//    }
//
//    consume(σEmp \ insγ, h, FullPerm(), predicate.body, pve, c2)((h1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
//      val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false)
//        //                  println(s"\nh1 = $h1")
//        //                  println(s"c3.reserveHeaps.head = ${c3.reserveHeaps.head}")
//        //                  println(s"c3.evalHeap = ${c3.evalHeap}")
//        consume(σ \ (γ = insγ, h = h1), h1, FullPerm(), predicate.body, pve, c3a)((h2, snap, _, c3b) => { /* σUsed'.fold */
//          /* TODO: Produce evaluated eArgs again - in evalHeap, which
//           * we otherwise shouldn't need. We could avoid this by
//           *   i) replacing each eArg by a fresh variable which we bind to the corresponding tArg
//           *      (to improve error reporting, a map from new to original node could be added to the context)
//           *   ii) or by adding a map from eArg to tArg to the context, and by modifying the
//           *       evaluator s.t. the mapping is used, if it exists
//           */
//          produce(σ \ h2, s => snap.convert(s), tPerm, acc, pve, c3b.copy(evalHeap = Some(c3.reserveHeaps.head)))((σ2, c4) => { /* σ2.h = σUsed'' */
//          val topReserveHeap = c3.reserveHeaps.head + σ2.h
//            val c4a = c4.decCycleCounter(predicate)
//                .copy(reserveHeaps = topReserveHeap +: c3.reserveHeaps.tail,
//                  exhaleExt = c3.exhaleExt,
//                  evalHeap = None)
//            consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4a)((h3, _, _, c5) =>
//              Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})})})
  }
}
