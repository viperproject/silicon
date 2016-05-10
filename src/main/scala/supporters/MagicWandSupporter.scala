/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import scala.util.control.Breaks._
import org.slf4s.{LoggerFactory, Logging}
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.{InternalReason, NegativePermission, InsufficientPermission}
import viper.silver.ast.utility.{Nodes, Visitor}
import viper.silver.verifier.errors._
import viper.silicon._
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.state.factoryUtils.Ø
import viper.silicon.decider.PathConditionStack
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNoAccess, IsNonNegative}

trait MagicWandSupporter[ST <: Store[ST],
                         H <: Heap[H],
                         S <: State[ST, H, S]]
    { this:      Logging
            with Evaluator[ST, H, S, DefaultContext[H]]
            with Producer[ST, H, S, DefaultContext[H]]
            with Consumer[ST, H, S, DefaultContext[H]] =>

  private[this] type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, DefaultContext[H]]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val heapCompressor: HeapCompressor[ST, H, S, DefaultContext[H]]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config
  protected val predicateSupporter: PredicateSupporter[ST, H, S, C]
  protected val chunkSupporter: ChunkSupporter[ST, H, S, C]

  import decider.{fresh, locally}
  import stateFactory._

  object magicWandSupporter {
    def checkWandsAreSelfFraming(γ: ST, g: H, root: ast.Member, c: C): VerificationResult = {
      val wands = Visitor.deepCollect(List(root), Nodes.subnodes){case wand: ast.MagicWand => wand}
      var result: VerificationResult = Success()

      //    println("\n[checkWandsAreSelfFraming]")

      breakable {
        wands foreach {_wand =>
          val err = MagicWandNotWellformed(_wand)

          /* NOTE: Named wand, i.e. "wand w := A --* B", are currently not (separately) checked for
           * self-framingness; instead, each such wand is replaced by "true --* true" (for the scope
           * of the self-framingness checks implemented in this block of code).
           * The reasoning here is that
           *   (1) either A --* B is a wand that is actually used in the program, in which case
           *       the other occurrences will be checked for self-framingness
           *   (2) or A --* B is a wand that does not actually occur in the program, in which case
           *       the verification will fail anyway
           */
          val trivialWand = (p: ast.Position) => ast.MagicWand(ast.TrueLit()(p), ast.TrueLit()(p))(p)
          val wand = _wand.transform {
            case v: ast.AbstractLocalVar if v.typ == ast.Wand => trivialWand(v.pos)
          }()

          val left = wand.left
          val right = wand.withoutGhostOperations.right
          val vs = Visitor.deepCollect(List(left, right), Nodes.subnodes){case v: ast.AbstractLocalVar => v}
          val γ1 = Γ(vs.map(v => (v, fresh(v))).toIterable) + γ
          val σ1 = Σ(γ1, Ø, g)

          //        println(s"  left = $left")
          //        println(s"  right = $right")
          //        println(s"  s1.γ = ${σ1.γ}")
          //        println(s"  s1.h = ${σ1.h}")
          //        println(s"  s1.g = ${σ1.g}")

          var σInner: S = null.asInstanceOf[S]

          result =
              locally {
                //            println("  checking left")
                produce(σ1, fresh, terms.FullPerm(), left, err, c)((σ2, c2) => {
                  σInner = σ2
                  //              val c3 = c2 /*.copy(givenHeap = Some(σ2.h))*/
                  //              val σ3 = σ1
                  Success()})
              } && locally {
                //            println("  checking right")
                produce(σ1, fresh, terms.FullPerm(), right, err, c.copy(lhsHeap = Some(σInner.h)))((_, c4) =>
                  Success())}

          //        println(s"  result = $result")

          result match {
            case failure: Failure =>
              /* Failure occurred. We transform the original failure into a MagicWandNotWellformed one. */
              result = failure.copy(message = MagicWandNotWellformed(wand, failure.message.reason))
              break()

            case _: NonFatalResult => /* Nothing needs to be done*/
          }
        }
      }

      result
    }

    def isDirectWand(exp: ast.Exp) = exp match {
      case wand: ast.MagicWand => true
      case v: ast.AbstractLocalVar => v.typ == ast.Wand
      case _ => false
    }

    def createChunk(σ: S, wand: ast.MagicWand, pve: PartialVerificationError, c: C)
                   (Q: (MagicWandChunk, C) => VerificationResult)
                   : VerificationResult = {

      val c0 = c.copy(exhaleExt = false)
      val ghostFreeWand = wand.withoutGhostOperations
      val es = ghostFreeWand.subexpressionsToEvaluate(c.program)

      evals(σ, es, _ => pve, c0)((ts, c1) => {
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
                                 name: String,
                                 args: Seq[Term],
                                 pLoss: Term,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C)
                                (Q: (Stack[H], Stack[Option[BasicChunk]], C) => VerificationResult)
                                : VerificationResult = {

      var toLose = pLoss
      var heapsToVisit = hs
      var visitedHeaps: List[H] = Nil
//      var chunks: List[DirectChunk] = Nil
      var cCurr = c
      val consumedChunks: Array[Option[BasicChunk]] = Array.fill(hs.length)(None)

//      println("\n[consumeFromMultipleHeaps]")
//      println(s"  heaps = ${hs.length}")
//      println(s"  toLose = $toLose")
//      println(s"  heapsToVisit = $heapsToVisit")
//      println(s"  visitedHeaps = $visitedHeaps")
//      println(s"  consumedChunks = $consumedChunks")

      while (heapsToVisit.nonEmpty && !decider.check(σ, IsNoAccess(toLose), config.checkTimeout())) {
        val h = heapsToVisit.head
        heapsToVisit = heapsToVisit.tail

//        println(s"\n  h = $h")
        val (h1, optCh1, toLose1, c1) = consumeMaxPermissions(σ, h, name, args, toLose, cCurr)
//        println(s"  h1 = $h1")
//        println(s"  optCh1 = $optCh1")
//        println(s"  toLose1 = $toLose1")

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

//      println(s"\n  X toLose = $toLose")
//      println(s"  X heapsToVisit = $heapsToVisit")
//      println(s"  X visitedHeaps = $visitedHeaps")
//      println(s"  X consumedChunks = $consumedChunks")
//      println(s"  X done? ${decider.check(σ, IsNoAccess(toLose))}")

      if (decider.check(σ, IsNoAccess(toLose), config.checkTimeout())) {
        val tEqs =
          consumedChunks.flatten.sliding(2).map {
            case Array(ch1: BasicChunk, ch2: BasicChunk) => ch1.snap === ch2.snap
            case _ => True()
          }

        decider.assume(toSet(tEqs))

        Q(visitedHeaps.reverse ++ heapsToVisit, consumedChunks, cCurr)
      } else
        Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
    }

    /* TODO: This is similar, but not as general, as the consumption algorithm
     *       implemented for supporting quantified permissions. It should be
     *       possible to unite the two.
     *
     * TODO: decider.getChunk will return the first chunk it finds - and only
     *       the first chunk. That is, if h contains multiple chunks for the
     *       given id, only the first one will be considered. This may result
     *       in missing permissions that could be taken from h.
     */
    private def consumeMaxPermissions(σ: S,
                                      h: H,
                                      name: String,
                                      args: Seq[Term],
                                      pLoss: Term,
                                      c: C)
                                     : (H, Option[BasicChunk], Term, C) = {

      chunkSupporter.getChunk(σ, h, name, args, c) match {
        case result @ Some(ch) =>
          val (pLost, pKeep, pToConsume) =
            if (decider.check(σ, PermAtMost(pLoss, ch.perm), config.checkTimeout()))
              (pLoss, PermMinus(ch.perm, pLoss), NoPerm())
            else
              (ch.perm, NoPerm(), PermMinus(pLoss, ch.perm))
  //        println("  [consumeMaxPermissions]")
  //        println(s"    ch.perm = ${ch.perm}")
  //        println(s"    pLost = $pLost")
  //        println(s"    pKeep = $pKeep")
  //        println(s"    pToConsume = $pToConsume")
          val h1 =
            if (decider.check(σ, IsNoAccess(pKeep), config.checkTimeout())) h - ch
            else h - ch + (ch \ pKeep)
          val consumedChunk = ch \ pLost
          (h1, Some(consumedChunk), pToConsume, c)

        case None => (h, None, pLoss, c)
      }
    }

    private var cnt = 0L
    private val packageLogger = LoggerFactory.getLogger("package")

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
      val allProducedChunks: MMap[Stack[Term], MList[BasicChunk]] = MMap()
      val allConsumedChunks: Stack[MMap[Stack[Term], MList[BasicChunk]]] = Stack.fill(stackSize)(MMap())

      var contexts: Seq[C] = Nil
      var magicWandChunk: MagicWandChunk = null

//      decider.pushScope()

      var pcsFromHeapIndepExprs = Vector[PathConditionStack]()

      val r = locally {
        produce(σEmp, fresh, FullPerm(), wand.left, pve, c0)((σLhs, c1) => {
          val c2 = c1.copy(reserveHeaps = c.reserveHeaps.head +: σLhs.h +: c.reserveHeaps.tail, /* [CTX] */
                           exhaleExt = true,
                           lhsHeap = Some(σLhs.h),
                           recordEffects = true,
                           producedChunks = Nil,
                           consumedChunks = Stack.fill(stackSize)(Nil))
          say(s"done: produced LHS ${wand.left}")
          say(s"next: consume RHS ${wand.right}")
          consume(σEmp, FullPerm(), wand.right, pve, c2)((σ1, _, c3) => {
            val c4 = c3.copy(recordEffects = false,
                             producedChunks = Nil,
                             consumedChunks = Stack(),
                             letBoundVars = Nil)
            say(s"done: consumed RHS ${wand.right}")
            say(s"next: create wand chunk")
            val preMark = decider.setPathConditionMark()
            magicWandSupporter.createChunk(σ \+ Γ(c3.letBoundVars), wand, pve, c4)((ch, c5) => {
              say(s"done: create wand chunk: $ch")
              pcsFromHeapIndepExprs :+= decider.pcs.after(preMark)
              magicWandChunk = ch
                /* TODO: Assert that all produced chunks are identical (due to
                 * branching, we might get here multiple times per package).
                 */

              lnsay(s"-- reached local end of packageWand $myId --")
              say(s"c3.producedChunks = ${c3.producedChunks}", 2)

              val producedChunks: MMap[Stack[Term], MList[BasicChunk]] = MMap()

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

              assert(c3.consumedChunks.length <= allConsumedChunks.length)
                /* c3.consumedChunks can have fewer layers due to infeasible execution paths,
                 * as illustrated by test case wands/regression/folding_inc1.sil.
                 * Hence the at-most comparison.
                 */

              val consumedChunks: Stack[MMap[Stack[Term], MList[BasicChunk]]] =
                c3.consumedChunks.map(pairs => {
                  val cchs: MMap[Stack[Term], MList[BasicChunk]] = MMap()

                  pairs.foreach {
                    case (guards, chunk) => cchs.getOrElseUpdate(guards, MList()) += chunk
                  }

                  cchs
                })

              say(s"consumedChunks:", 2)
              consumedChunks.foreach(x => say(x.toString(), 3))

              assert(consumedChunks.length <= allConsumedChunks.length)
                /* At-most comparison due to infeasible execution paths */

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
              Success()})})})}

//      decider.popScope()

      cnt -= 1
      lnsay(s"[end packageWand $myId]")

      say(s"produced magic wand chunk $magicWandChunk")
      say(s"allProducedChunks = $allProducedChunks")
      say(s"allConsumedChunks:")
      allConsumedChunks.foreach(x => say(x.toString(), 2))
      say(s"recorded ${contexts.length} contexts")
      contexts.foreach(c => c.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2)))

      r && {
        assert(contexts.isEmpty == (magicWandChunk == null))

        if (magicWandChunk == null) {
          /* magicWandChunk is still null, i.e. no wand chunk was produced. This
           * should only happen if the wand is inconsistent, i.e. if the symbolic
           * execution pruned all branches (during the package operation) before
           * reaching the point at which a wand chunk is created and assigned to
           * magicWandChunk.
           */
          assert(!wand.contains[ast.Let])
            /* TODO: magicWandSupporter.createChunk expects a store that already
             * binds variables that are let-bound in the wand.
             * In the case where the symbolic execution does not prune all branches,
             * the bindings are taken from the context (see call to createChunk
             * above).
             */

          val c1 = c.copy(reserveHeaps = c.reserveHeaps.head +: H() +: c.reserveHeaps.tail) /* IMPORTANT: Must match structure of [CTX] above */
          magicWandSupporter.createChunk(σ, wand, pve, c1)((ch, c2) => {
            say(s"done: create wand chunk: $ch")
            Q(ch, c2)})
        } else {
          lnsay("Restoring path conditions obtained from evaluating heap-independent expressions")
          pcsFromHeapIndepExprs.foreach(pcs => decider.assume(pcs.asConditionals))

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
                case fc: FieldChunk =>
                  joinedReserveHeaps.head.transform {
                    case ch1: BasicChunk if ch1.args == fc.args && ch1.name == fc.name =>
                      added = true
                      fc.copy(perm = PermPlus(ch1.perm, pGain))
                    case ch1 => ch1
                  }

                case pc: PredicateChunk =>
                  joinedReserveHeaps.head.transform {
                    case ch1: BasicChunk if ch1.args == pc.args && ch1.name == pc.name =>
                      added = true
                      pc.copy(perm = PermPlus(ch1.perm, pGain))
                    case ch1 => ch1
                  }

//                case qc: QuantifiedChunk => sys.error(s"Unexpectedly found a quantified chunk: $QuantifiedChunk")
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
                  case fc: FieldChunk =>
                    hR.transform {
                      case ch1: BasicChunk if ch1.args == fc.args && ch1.name == fc.name =>
                        matched = true
                        fc.copy(perm = PermMinus(ch1.perm, pLoss))
                      case ch1 => ch1
                    }

                  case pc: PredicateChunk =>
                    hR.transform {
                      case ch1: BasicChunk if ch1.args == pc.args && ch1.name == pc.name =>
                        matched = true
                        pc.copy(perm = PermMinus(ch1.perm, pLoss))
                      case ch1 => ch1
                    }

//                  case qc: QuantifiedChunk => sys.error(s"Unexpectedly found a quantified chunk: $QuantifiedChunk")
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

          val consumedChunks: Stack[Seq[(Stack[Term], BasicChunk)]] =
            allConsumedChunks.zip(c.consumedChunks.head +: Nil +: c.consumedChunks.tail).map { case (allcchs, cchs) =>
              cchs ++ allcchs.toSeq.flatMap { case (guards, chunks) => chunks.map(ch => (guards, ch))}}

          lnsay(s"Exiting packageWand $myId. Final consumedChunks:")
          consumedChunks.foreach(x => say(x.toString(), 2))

          /* TODO: Merge contexts */
          val c1 = contexts.head.copy(reserveHeaps = joinedReserveHeaps.map(H(_)),
                                      recordEffects = c.recordEffects,
                                      producedChunks = c.producedChunks,
                                      consumedChunks = consumedChunks/*,
                                      branchConditions = c.branchConditions*/)

          Q(magicWandChunk, c1)
        }
      }
    }

    def applyingWand(σ: S, γ: ST, wand: ast.MagicWand, lhsAndWand: ast.Exp, pve: PartialVerificationError, c: C)
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
      consume(σEmp \ σ0.h, FullPerm(), lhsAndWand, pve, c0a)((σ1, _, c1) => { /* exhale_ext, σ1.h = σUsed' */
        val c1a = c1.copy(reserveHeaps = Nil, exhaleExt = false)
        consume(σ0 \ σ1.h, FullPerm(), lhsAndWand, pve, c1a)((σ2, _, c2) => { /* σUsed'.apply */
          val c2a = c2.copy(lhsHeap = Some(σ1.h))
          produce(σ0 \ σ2.h, decider.fresh, FullPerm(), wand.right, pve, c2a)((σ3, c3) => { /* σ3.h = σUsed'' */
            val topReserveHeap = heapCompressor.merge(σ3, c1.reserveHeaps.head, σ3.h, c)
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
          if (decider.check(σC, IsNonNegative(tPerm), config.checkTimeout()))
            evals(σC, eArgs, _ => pve, c1)((tArgs, c2) =>
              consume(σEmp \ σ.h, FullPerm(), acc, pve, c2)((σ1, _, c3) => { /* exhale_ext, h1 = σUsed' */
                val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false)
                predicateSupporter.unfold(σ \ σ1.h, predicate, tArgs, tPerm, pve, c3a, pa)((σ3, c4) => { /* σ2.h = σUsed'' */
                  val topReserveHeap = heapCompressor.merge(σ3, c3.reserveHeaps.head, σ3.h, c)
                  val c4a = c4.decCycleCounter(predicate)
                              .copy(reserveHeaps = topReserveHeap +: c3.reserveHeaps.tail,
                                    exhaleExt = c3.exhaleExt)
                  QI(σEmp, σEmp.h, c4a)})}))
          else
            Failure(pve dueTo NegativePermission(ePerm)))
      } else {
        Failure(pve dueTo InternalReason(acc, "Too many nested unfolding ghost operations."))
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
        evals(σC, eArgs, _ => pve, c0)((tArgs, c1) =>
          eval(σC, ePerm, pve, c1)((tPerm, c2) =>
            decider.assert(σ, IsNonNegative(tPerm)) {
              case true =>
                foldingPredicate(σ, predicate, tArgs, tPerm, pve, c2, Some(pa))((σ1, h1, c3) =>
                  QI(σEmp, σEmp.h, c3.decCycleCounter(predicate)))
            case false =>
              Failure(pve dueTo NegativePermission(ePerm))}))
      } else
        Failure(pve dueTo InternalReason(acc, "Too many nested folding ghost operations."))
    }

    def foldingPredicate(σ: S,
                         predicate: ast.Predicate,
                         tArgs: List[Term],
                         tPerm: Term,
                         pve: PartialVerificationError,
                         c: C,
                         optPA: Option[ast.PredicateAccess] = None)
                        (Q: (S, H, C) => VerificationResult)
                        : VerificationResult = {

      /* [2014-12-13 Malte] Changing the store doesn't interact well with the
       * snapshot recorder, see the comment in PredicateSupporter.unfold.
       * However, since folding cannot (yet) be used inside functions, we can
       * still overwrite the binding of local variables in the store.
       * An alternative would be to introduce fresh local variables, and to
       * inject them into the predicate body. See commented code below.
       *
       * Note: If fresh local variables are introduced here, we should avoid
       * introducing another sequence of local variables inside predicateSupporter.fold!
       */
      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
      val body = predicate.body.get /* Only non-abstract predicates can be folded */
      val σEmp = Σ(σ.γ + insγ, Ø, σ.g)
      //      val args = predicate.formalArgs.map(fa => ast.utils.fresh(fa.localVar))
      //      val body = Expressions.instantiateVariables(predicate.body, predicate.formalArgs, args)
      //      val σEmp = Σ(σ.γ + Γ(args.zip(tArgs)), Ø, σ.g)

      consume(σEmp \ σ.h, tPerm, body, pve, c)((σ1, _, c1) => { /* exhale_ext, σ1 = σUsed' */
        val c2 = c1.copy(reserveHeaps = Nil, exhaleExt = false)
        predicateSupporter.fold(σ \ σ1.h, predicate, tArgs, tPerm, pve, c2)((σ2, c3) => { /* σ2.h = σUsed'' */
          val topReserveHeap = c1.reserveHeaps.head + σ2.h
          val c4 = c3.copy(reserveHeaps = topReserveHeap +: c1.reserveHeaps.tail,
                           exhaleExt = c1.exhaleExt)
          Q(σEmp \ σ.γ, σEmp.h, c4)})})
    }

    /* Function "transfer" from wands paper.
     * Permissions are transferred from the stack of heaps to σUsed, which is
     * h in the current context.
     */
    def transfer(σ: S,
                 h: H,
                 name: String,
                 args: Seq[Term],
                 perms: Term,
                 locacc: ast.LocationAccess,
                 pve: PartialVerificationError,
                 c: C)
                (Q: (H, Option[BasicChunk], C) => VerificationResult)
                : VerificationResult = {

      magicWandSupporter.consumeFromMultipleHeaps(σ, c.reserveHeaps, name, args, perms, locacc, pve, c)((hs, chs, c1/*, pcr*/) => {
        val c2 = c1.copy(reserveHeaps = hs)
        val c3 =
          if (c2.recordEffects) {
            assert(chs.length == c2.consumedChunks.length)
            val bcs = decider.pcs.branchConditions
            val consumedChunks3 =
              chs.zip(c2.consumedChunks).foldLeft(Stack[Seq[(Stack[Term], BasicChunk)]]()) {
                case (accConsumedChunks, (optCh, consumed)) =>
                  optCh match {
                    case Some(ch) => ((bcs -> ch) +: consumed) :: accConsumedChunks
                    case None => consumed :: accConsumedChunks
                  }
              }.reverse

            c2.copy(consumedChunks = consumedChunks3)
          } else
            c2

        val usedChunks = chs.flatten
        /* Returning any of the usedChunks should be fine w.r.t to the snapshot
         * of the chunk, since consumeFromMultipleHeaps should have equated the
         * snapshots of all usedChunks.
         */
        Q(h + H(usedChunks), usedChunks.headOption, c3)})
    }

    def getEvalHeap(σ: S, h: H, c: C): H = {
      if (c.exhaleExt) c.reserveHeaps.headOption.fold(h)(h + _)
      else σ.h
    }

    def getMatchingChunk(σ: S, h: H, chunk: MagicWandChunk, c: C): Option[MagicWandChunk] = {
      val mwChunks = h.values.collect { case ch: MagicWandChunk => ch }
      mwChunks.find(ch => compareWandChunks(σ, chunk, ch, c))
    }

    private def compareWandChunks(σ: S,
                                  chWand1: MagicWandChunk,
                                  chWand2: MagicWandChunk,
                                  c: C)
                                 : Boolean = {
  //    println(s"\n[compareWandChunks]")
  //    println(s"  chWand1 = ${chWand1.ghostFreeWand}")
  //    println(s"  chWand2 = ${chWand2.ghostFreeWand}")
      var b = chWand1.ghostFreeWand.structurallyMatches(chWand2.ghostFreeWand, c.program)
  //    println(s"  after structurallyMatches: b = $b")
      b = b && chWand1.evaluatedTerms.length == chWand2.evaluatedTerms.length
  //    println(s"  after comparing evaluatedTerms.length's: b = $b")
      b = b && decider.check(σ, And(chWand1.evaluatedTerms zip chWand2.evaluatedTerms map (p => p._1 === p._2)), config.checkTimeout())
  //    println(s"  after comparing evaluatedTerms: b = $b")

      b
    }
  }
}
