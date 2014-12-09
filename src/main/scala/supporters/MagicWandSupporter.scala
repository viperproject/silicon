package viper
package silicon
package supporters

import com.weiglewilczek.slf4s.{Logger, Logging}
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{InternalReason, NegativePermission, InsufficientPermission}
import interfaces.{Success, Evaluator, Consumer, Producer, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.state.{StateFormatter, StateFactory, Chunk, ChunkIdentifier, State, PathConditions, Heap, Store}
import interfaces.state.factoryUtils.Ø
import state.{DefaultContext, DirectChunk, DirectPredicateChunk, DirectFieldChunk, MagicWandChunk}
import state.terms._
import state.terms.perms.{IsNoAccess, IsAsPermissive, IsNonNegative}

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

//  protected val symbolConverter: SymbolConvert
//  import symbolConverter.toSort

  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config

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

      val c0 = c.copy(exhaleExt = false)
      val ghostFreeWand = wand.withoutGhostOperations
      val es = ghostFreeWand.subexpressionsToEvaluate(c.program)

      evals(σ, es, pve, c0)((ts, c1) => {
        val c2 = c1.copy(exhaleExt = c.exhaleExt)
        Q(MagicWandChunk(ghostFreeWand, σ.γ.values, ts), c2)})
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
                                (Q: (Stack[H], Stack[Option[DirectChunk]], C) => VerificationResult)
                                : VerificationResult = {

      var toLose = pLoss
      var heapsToVisit = hs
      var visitedHeaps: List[H] = Nil
//      var chunks: List[DirectChunk] = Nil
      var cCurr = c
      val consumedChunks: Array[Option[DirectChunk]] = Array.fill(hs.length)(None)

//      println("\n[consumeFromMultipleHeaps]")
//      println(s"  heaps = ${hs.length}")
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
//        chunks =
//          optCh1 match {
//            case None => chunks
//  //          case Some(ch) => (ch, visitedHeaps.length  - 1) :: chunks
//            case Some(ch) => ch :: chunks
//          }
        assert(consumedChunks(hs.length - 1 - heapsToVisit.length).isEmpty)
        consumedChunks(hs.length - 1 - heapsToVisit.length) = optCh1
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
          consumedChunks.flatten.sliding(2).map {
  //          case List((fc1: DirectFieldChunk, _), (fc2: DirectFieldChunk, _)) => fc1.value === fc2.value
            case Array(fc1: DirectFieldChunk, fc2: DirectFieldChunk) => fc1.value === fc2.value
  //          case List((pc1: DirectPredicateChunk, _), (pc2: DirectPredicateChunk, _)) => pc1.snap === pc2.snap
            case Array(pc1: DirectPredicateChunk, pc2: DirectPredicateChunk) => pc1.snap === pc2.snap
            case _ => True()
          }

        decider.assume(toSet(tEqs))

        Q(visitedHeaps.reverse ++ heapsToVisit, consumedChunks, cCurr)
      } else {
        val f = Failure[ST, H, S](pve dueTo InsufficientPermission(locacc))
        f.load = id.args

        f
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

    private var cnt = 0L
    private val packageLogger = Logger("package")

    def packageWand(σ: S, wand: ast.MagicWand, pve: PartialVerificationError, c: C)
                   (Q: (MagicWandChunk, C) => VerificationResult)
                   : VerificationResult = {

      val σEmp = Σ(σ.γ, Ø, σ.g)
      val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)

      /* TODO: Logging code is very similar to that in HeuristicsSupporter. Unify. */
      val myId = cnt; cnt += 1
      val baseIdent = "  "
      var printedHeader = false

      def lnsay(msg: String, ident: Int = 1) {
        val prefix = "\n" + (if (ident == 0) "" else baseIdent)
        dosay(prefix, msg, ident - 1)
      }

      def say(msg: String, ident: Int = 1) {
        val prefix = if (ident == 0) "" else baseIdent
        dosay(prefix, msg, ident - 1)
      }

      def dosay(prefix: String, msg: String, ident: Int) {
        if (!printedHeader) {
          packageLogger.debug(s"\n[packageWand $myId]")
          printedHeader = true
        }

        val messagePrefix = baseIdent * ident
        packageLogger.debug(s"$prefix$messagePrefix $msg")
      }

      say(s"wand = $wand")
      say(s"c.producedChunks = ${c.producedChunks}")
      say("c.reserveHeaps:")
      c.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2))

      val stackSize = c.reserveHeaps.length + 1 /* IMPORTANT: Must match size of reserveHeaps at [CTX] below */
      val allProducedChunks: MMap[Stack[Term], MList[DirectChunk]] = MMap()
      val allConsumedChunks: Stack[MMap[Stack[Term], MList[DirectChunk]]] = Stack.fill(stackSize)(MMap())

      var contexts: Seq[C] = Nil
      var magicWandChunk: MagicWandChunk = null

      decider.pushScope()

      val r =
        produce(σEmp, fresh, FullPerm(), wand.left, pve, c0)((σLhs, c1) => {
          val c2 = c1.copy(reserveHeaps = c.reserveHeaps.head +: σLhs.h +: c.reserveHeaps.tail, /* [CTX] */
                           exhaleExt = true,
                           lhsHeap = Some(σLhs.h),
                           recordEffects = true,
                           producedChunks = Nil,
                           consumedChunks = Stack.fill(stackSize)(Nil))
          consume(σEmp, FullPerm(), wand.right, pve, c2)((_, _, _, c3) => {
            val c4 = c3.copy(recordEffects = false,
                             producedChunks = Nil,
                             consumedChunks = Stack())
            magicWandSupporter.createChunk(σ, wand, pve, c4)((ch, c5) => {
              magicWandChunk = ch

              lnsay(s"-- reached local end of packageWand $myId --")
              say(s"c3.producedChunks = ${c3.producedChunks}", 2)

              val producedChunks: MMap[Stack[Term], MList[DirectChunk]] = MMap()

              c3.producedChunks.foreach{ case (guards, chunk) =>
                producedChunks.getOrElseUpdate(guards, MList()) += chunk}

              say(s"producedChunks = $producedChunks", 2)

              producedChunks.foreach{ case (guards, chunks) =>
                allProducedChunks.get(guards) match {
                  case Some(chunks1) => assert(chunks1 == chunks)
                  case None => allProducedChunks(guards) = chunks
                }
              }

              say(s"allProducedChunks = $allProducedChunks", 2)
              lnsay(s"c3.consumedChunks:", 2)
              c3.consumedChunks.foreach(x => say(x.toString(), 3))

              assert(c3.consumedChunks.length == allConsumedChunks.length)

              val consumedChunks: Stack[MMap[Stack[Term], MList[DirectChunk]]] =
                c3.consumedChunks.map(pairs => {
                  val cchs: MMap[Stack[Term], MList[DirectChunk]] = MMap()

                  pairs.foreach {
                    case (guards, chunk) => cchs.getOrElseUpdate(guards, MList()) += chunk
                  }

                  cchs
                })

              say(s"consumedChunks:", 2)
              consumedChunks.foreach(x => say(x.toString(), 3))

              assert(consumedChunks.length == allConsumedChunks.length)

              consumedChunks.zip(allConsumedChunks).foreach { case (cchs, allcchs) =>
                cchs.foreach { case (guards, chunks) =>
                  allcchs.get(guards) match {
                    case Some(chunks1) => assert(chunks1 == chunks)
                    case None => allcchs(guards) = chunks
                  }
                }
              }

              say(s"allConsumedChunks:", 2)
              allConsumedChunks.foreach(x => say(x.toString(), 3))

              contexts :+= c5
              Success()})})})

      decider.popScope()

      cnt -= 1
      lnsay(s"[end packageWand $myId]")

      say(s"produced magic wand chunk $magicWandChunk")
      say(s"allProducedChunks = $allProducedChunks")
      say(s"allConsumedChunks:")
      allConsumedChunks.foreach(x => say(x.toString(), 2))
      say(s"recorded ${contexts.length} contexts")
      contexts.foreach(c => c.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2)))

      r && {
        assert(contexts.map(_.reserveHeaps).map(_.length).toSet.size == 1)

        val joinedReserveHeaps: Stack[MList[Chunk]] = ( /* IMPORTANT: Must match structure of [CTX] above */
               (MList() ++ c.reserveHeaps.head.values)
            +: MList[Chunk]() /* σLhs.h at [CTX] above */
            +: c.reserveHeaps.tail.map(h => MList() ++ h.values)
          )

        assert(joinedReserveHeaps.length == stackSize)

        lnsay("Computing joined reserve heaps. Initial stack:")
        joinedReserveHeaps.foreach(x => say(x.toString(), 2))

        allProducedChunks.foreach { case (guards, chunks) =>
          chunks.foreach(ch => {
            val pGain = Ite(And(guards), ch.perm, NoPerm())
            var added = false

            ch match {
              case fc: DirectFieldChunk =>
                joinedReserveHeaps.head.transform {
                  case ch1: DirectChunk if ch1.args == fc.args && ch1.name == fc.name =>
                    added = true
                    fc.copy(perm = PermPlus(ch1.perm, pGain))
                  case ch1 => ch1
                }

              case pc: DirectPredicateChunk =>
                joinedReserveHeaps.head.transform {
                  case ch1: DirectChunk if ch1.args == pc.args && ch1.name == pc.name =>
                    added = true
                    pc.copy(perm = PermPlus(ch1.perm, pGain))
                  case ch1 => ch1
                }
            }

            if (!added) joinedReserveHeaps.head += ch
          })
        }

        lnsay("Stack after adding allProducedChunks:")
        joinedReserveHeaps.foreach(x => say(x.toString(), 2))

        /* Replace the second top-most layer of allConsumedChunks with Nil
         * because we don't want to (and din't need to) replay the effects on
         * the that layer since it corresponds to the LHS heap.
         * The corresponding level in joinedReserveHeaps is empty, and we thus
         * cannot consume from it anyway.
         */
        joinedReserveHeaps.zip(allConsumedChunks.head +: Nil +: allConsumedChunks.drop(2)).foreach { case (hR, allcchs) =>
          allcchs.foreach { case (guards, chunks) =>
            chunks.foreach(ch => {
              val pLoss = Ite(And(guards), ch.perm, NoPerm())
              var matched = false

              ch match {
                case fc: DirectFieldChunk =>
                  hR.transform {
                    case ch1: DirectChunk if ch1.args == fc.args && ch1.name == fc.name =>
                      matched = true
                      fc.copy(perm = PermMinus(ch1.perm, pLoss))
                    case ch1 => ch1
                  }

                case pc: DirectPredicateChunk =>
                  hR.transform {
                    case ch1: DirectChunk if ch1.args == pc.args && ch1.name == pc.name =>
                      matched = true
                      pc.copy(perm = PermMinus(ch1.perm, pLoss))
                    case ch1 => ch1
                  }
              }

              if (!matched) {
                say(s"Couldn't find a match for $ch!")
                say(s"hR = $hR", 2)
                say(s"guards = $guards", 2)
                say(s"chunks = $chunks", 2)
                assert(matched)
              }
            })
        }}

        lnsay("Finished joined reserve heaps. Final stack:")
        joinedReserveHeaps.foreach(x => say(x.toString(), 2))

        assert(allConsumedChunks.length == c.consumedChunks.length + 1)

        val consumedChunks: Stack[Seq[(Stack[Term], DirectChunk)]] =
          allConsumedChunks.zip(c.consumedChunks.head +: Nil +: c.consumedChunks.tail).map { case (allcchs, cchs) =>
            cchs ++ allcchs.toSeq.flatMap { case (guards, chunks) => chunks.map(ch => (guards, ch))}}

        lnsay(s"Exiting packageWand $myId. Final consumedChunks:")
        consumedChunks.foreach(x => say(x.toString(), 2))

        /* TODO: Merge contexts */
        val c1 = contexts(0).copy(reserveHeaps = joinedReserveHeaps.map(H(_)),
                                  recordEffects = c.recordEffects,
                                  producedChunks = c.producedChunks,
                                  consumedChunks = consumedChunks)

        Q(magicWandChunk, c1)
      }
    }

    def applyingWand(σ: S, γ: ST, wand: ast.MagicWand, lhsAndWand: ast.Expression, pve: PartialVerificationError, c: C)
                    (QI: (S, H, C) => VerificationResult)
                    : VerificationResult = {

      val σ0 = σ \ γ
      val σEmp = Σ(σ0.γ, Ø, σ0.g)
      val c0a = c.copy(applyHeuristics = false)
        /* Triggering heuristics, in particular, ghost operations (apply-/packag-/(un)folding)
         * during the first consumption of lhsAndWand doesn't work because the ghost operations
         * potentially affect the reserve heaps, and not σ1.h. Since the latter is used by
         * the second consumption of lhsAndWand, this might fail again. However, triggering
         * heuristics in this situation won't help much, since only σ1.h is available during
         * this consumption (but not the reserve heaps). Hence the second consumption is
         * likely to fail anyway.
         * Instead, the the whole invocation of applyingWand should be wrapped in a
         * tryOperation. This will ensure that the effect of ghost operations triggered by
         * heuristics are available to both consumes.
         */

      /* TODO: Actually use c0a. Probably means that all uses of applyingWand have to be wrapped in tryOperation
       * TODO: The same for unfoldingPredicate, foldingPredicate
       * TODO: What about packageWand?
       */
      consume(σEmp \ σ0.h, FullPerm(), lhsAndWand, pve, c0a)((σ1, _, chs1, c1) => { /* exhale_ext, σ1.h = σUsed' */
        assert(chs1.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
        val ch = chs1.last.asInstanceOf[MagicWandChunk]
        val c1a = c1.copy(reserveHeaps = Nil, exhaleExt = false)
        consume(σ0 \ σ1.h, FullPerm(), lhsAndWand, pve, c1a)((σ2, _, chs2, c2) => { /* σUsed'.apply */
          assert(chs2.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
          assert(ch == chs2.last.asInstanceOf[MagicWandChunk], s"Expected $chs1 == $chs2")
          val c2a = c2.copy(lhsHeap = Some(σ1.h))
          produce(σ0 \ σ2.h, decider.fresh, FullPerm(), wand.right, pve, c2a)((σ3, c3) => { /* σ3.h = σUsed'' */
            val topReserveHeap = c1.reserveHeaps.head + σ3.h
            val c3a = c3.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.tail,
                              exhaleExt = c1.exhaleExt,
                              lhsHeap = c2.lhsHeap,
                              applyHeuristics = c.applyHeuristics)
            QI(σEmp \ σ.γ, σEmp.h, c3a)})})})
    }

    def unfoldingPredicate(σ: S, acc: ast.PredicateAccessPredicate, pve: PartialVerificationError, c: C)
                          (QI: (S, H, C) => VerificationResult)
                          : VerificationResult = {

      val ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm) = acc
      val predicate = c.program.findPredicate(predicateName)

      if (c.cycles(predicate) < config.recursivePredicateUnfoldings()) {
        val c0 = c.incCycleCounter(predicate)
        val σC = σ \ getEvalHeap(σ, σ.h, c0)
        val σEmp = Σ(σ.γ, Ø, σ.g)
        eval(σC, ePerm, pve, c0)((tPerm, c1) =>
          if (decider.check(σC, IsNonNegative(tPerm)))
            evals(σC, eArgs, pve, c1)((tArgs, c2) =>
              consume(σEmp \ σ.h, FullPerm(), acc, pve, c2)((σ1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
              val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false, evalHeap = Some(c3.reserveHeaps.head))
                consume(σ \ σ1.h, FullPerm(), acc, pve, c3a)((σ2, snap, _, c3b) => { /* σUsed'.unfold */
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                  produce(σ \ σ2.h \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3b.copy(evalHeap = None))((σ3, c4) => { /* σ2.h = σUsed'' */ /* TODO: Substitute args in body */
                    val topReserveHeap = c3.reserveHeaps.head + σ3.h
                    val c4a = c4.decCycleCounter(predicate)
                                .copy(reserveHeaps = topReserveHeap +: c3.reserveHeaps.tail,
                                      exhaleExt = c3.exhaleExt)
                    QI(σEmp, σEmp.h, c4a)})})}))
          else
            Failure[ST, H, S](pve dueTo NegativePermission(ePerm)))
      } else {
        Failure[ST, H, S](pve dueTo InternalReason(acc, "Too many nested unfolding ghost operations."))
      }
    }

    def foldingPredicate(σ: S, acc: ast.PredicateAccessPredicate, pve: PartialVerificationError, c: C)
                        (QI: (S, H, C) => VerificationResult)
                        : VerificationResult = {

      val ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm) = acc
      val predicate = c.program.findPredicate(predicateName)

      if (c.cycles(predicate) < config.recursivePredicateUnfoldings()) {
        val c0 = c.incCycleCounter(predicate)
        val σC = σ \ magicWandSupporter.getEvalHeap(σ, σ.h, c0)
        val σEmp = Σ(σ.γ, Ø, σ.g)
        eval(σC, ePerm, pve, c0)((tPerm, c1) => {
          if (decider.check(σC, IsNonNegative(tPerm)))
            evals(σC, eArgs, pve, c1)((tArgs, c2) => {
              val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs) /* TODO: Substitute args in body */
              consume(σEmp \ σ.h \ insγ, FullPerm(), predicate.body, pve, c2)((σ1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
              val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false)
                consume(σ \ (γ = insγ, h = σ1.h), FullPerm(), predicate.body, pve, c3a)((σ2, snap, _, c3b) => { /* σUsed'.fold */
                  /* TODO: Produce evaluated eArgs again - in evalHeap, which
                   * we otherwise shouldn't need. We could avoid this by
                   *   i) replacing each eArg by a fresh variable which we bind to the corresponding tArg
                   *      (to improve error reporting, a map from new to original node could be added to the context)
                   *   ii) or by adding a map from eArg to tArg to the context, and by modifying the
                   *       evaluator s.t. the mapping is used, if it exists
                   */
                  produce(σ \ σ2.h, s => snap.convert(s), tPerm, acc, pve, c3b.copy(evalHeap = Some(c3.reserveHeaps.head)))((σ3, c4) => { /* σ3.h = σUsed'' */
                    val topReserveHeap = c3.reserveHeaps.head + σ3.h
                    val c4a = c4.decCycleCounter(predicate)
                                .copy(reserveHeaps = topReserveHeap +: c3.reserveHeaps.tail,
                                      exhaleExt = c3.exhaleExt,
                                      evalHeap = None)
                    QI(σEmp, σEmp.h, c4a)})})})})
          else
            Failure[ST, H, S](pve dueTo NegativePermission(ePerm))})
      } else
        Failure[ST, H, S](pve dueTo InternalReason(acc, "Too many nested folding ghost operations."))
    }

    def getEvalHeap(σ: S, h: H, c: C): H = {
      if (c.exhaleExt) c.reserveHeaps.headOption.fold(h)(h + _)
      else σ.h
    }
  }
}
