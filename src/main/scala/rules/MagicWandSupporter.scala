/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission
import viper.silicon._
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms.perms.IsNonPositive
import viper.silicon.state.terms.{MagicWandSnapshot, _}
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier
import viper.silver.ast.{Exp, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock

object magicWandSupporter extends SymbolicExecutionRules with Immutable {
  import evaluator._
  import producer._
  import consumer._

  def checkWandsAreSelfFraming(s: State, g: Store, oldHeap: Heap, root: ast.Member, v: Verifier): VerificationResult =
    sys.error("Implementation missing")
//  {
//    val wands = Visitor.deepCollect(List(root), Nodes.subnodes){case wand: ast.MagicWand => wand}
//    var result: VerificationResult = Success()
//
//    breakable {
//      wands foreach {_wand =>
//        val err = MagicWandNotWellformed(_wand)
//
//        /* NOTE: Named wand, i.e. "wand w := A --* B", are currently not (separately) checked for
//         * self-framingness; instead, each such wand is replaced by "true --* true" (for the scope
//         * of the self-framingness checks implemented in this block of code).
//         * The reasoning here is that
//         *   (1) either A --* B is a wand that is actually used in the program, in which case
//         *       the other occurrences will be checked for self-framingness
//         *   (2) or A --* B is a wand that does not actually occur in the program, in which case
//         *       the verification will fail anyway
//         */
//        val trivialWand = (p: ast.Position) => ast.MagicWand(ast.TrueLit()(p), ast.TrueLit()(p))(p)
//        val wand = _wand.transform {
//          case v: ast.AbstractLocalVar if v.typ == ast.Wand => trivialWand(v.pos)
//        }()
//
//        val left = wand.left
//        val right = wand.withoutGhostOperations.right
//        val vs = Visitor.deepCollect(List(left, right), Nodes.subnodes){case v: ast.AbstractLocalVar => v}
//        val γ1 = Γ(vs.map(v => (v, fresh(v))).toIterable) + γ
//        val σ1 = Σ(γ1, Ø, g)
//
//        var σInner: S = null.asInstanceOf[S]
//
//        result =
//          locallyXXX {
//            produce(σ1, fresh, left, err, c)((σ2, c2) => {
//              σInner = σ2
//              Success()})
//          } && locallyXXX {
//            produce(σ1, fresh, right, err, c.copy(lhsHeap = Some(σInner.h)))((_, c4) =>
//              Success())}
//
//        result match {
//          case failure: Failure =>
//            /* Failure occurred. We transform the original failure into a MagicWandNotWellformed one. */
//            result = failure.copy(message = MagicWandNotWellformed(wand, failure.message.reason))
//            break()
//
//          case _: NonFatalResult => /* Nothing needs to be done*/
//        }
//      }
//    }
//
//    result
//  }

  //TODO: needs to calculate a snapshot that preserves values from the lhs
  def createChunk(s: State,
                  wand: ast.MagicWand,
                  pve: PartialVerificationError,
                  v: Verifier)
                  (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                  : VerificationResult =
    createChunk(s, wand, None, pve, v)(Q)

  def createChunk(s: State,
                  wand: ast.MagicWand,
                  abstractLhs: Term,
                  rhsSnapshot: Term,
                  pve: PartialVerificationError,
                  v: Verifier)
                  (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                  : VerificationResult =
    createChunk(s, wand, Some((abstractLhs, rhsSnapshot)), pve, v)(Q)

  private def createChunk(s: State,
                          wand: ast.MagicWand,
                          possibleSnapshotPair: Option[(Term, Term)],
                          pve: PartialVerificationError,
                          v: Verifier)
                          (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                          : VerificationResult = {

    val s1 = s.copy(exhaleExt = false)
    val es = wand.subexpressionsToEvaluate(Verifier.program)

    evals(s1, es, _ => pve, v)((s2, ts, v1) => {
      val s3 = s2.copy(exhaleExt = s.exhaleExt)
      val snapshotPair = possibleSnapshotPair.getOrElse((freshSnap(sorts.Snap, v), freshSnap(sorts.Snap, v)))
      Q(s3, MagicWandChunk(MagicWandIdentifier(wand), s3.g.values, ts, MagicWandSnapshot(snapshotPair._1, snapshotPair._2), FullPerm()), v1)
  })}

  /* TODO: doWithMultipleHeaps and consumeFromMultipleHeaps have a similar
   *       structure. Try to merge the two.
   */

  def doWithMultipleHeaps[R](s: State,
                             hs: Stack[Heap],
                             v: Verifier)
                            (action: (State, Heap, Verifier) => (State, Option[R], Heap, Verifier))
                            (Q: (State, Option[R], Stack[Heap], Verifier) => VerificationResult)
                            : VerificationResult = {

    var heapsToVisit = hs
    var visitedHeaps: List[Heap] = Nil
    var rCurr: Option[R] = None
    var sCurr = s
    var vCurr = v

    while (heapsToVisit.nonEmpty && rCurr.isEmpty) {
      val h = heapsToVisit.head
      heapsToVisit = heapsToVisit.tail

      val (s1, r1, h1, v1) = action(sCurr, h, vCurr)
      visitedHeaps = h1 :: visitedHeaps
      rCurr = r1
      sCurr = s1
      vCurr = v1
    }

    Q(sCurr, rCurr, visitedHeaps.reverse ++ heapsToVisit, vCurr)
  }

  def consumeFromMultipleHeaps(s: State,
                               hs: Stack[Heap],
                               id: ChunkIdentifer,
                               args: Seq[Term],
                               pLoss: Term,
                               locacc: ast.LocationAccess,
                               pve: PartialVerificationError,
                               v: Verifier)
                              (Q: (State, Stack[Heap], Stack[Option[NonQuantifiedChunk]], Verifier) => VerificationResult)
                              : VerificationResult = {

    val consumedChunks: Array[Option[NonQuantifiedChunk]] = Array.fill(hs.length)(None)
    var toLose = pLoss
    var heapsToVisit = hs
    var visitedHeaps: List[Heap] = Nil
    var sCurr = s
    var vCurr = v

    while (heapsToVisit.nonEmpty && !v.decider.check(IsNonPositive(toLose), Verifier.config.checkTimeout())) {
      val h = heapsToVisit.head
      heapsToVisit = heapsToVisit.tail

      val (s1, h1, optCh1, toLose1, v1) = consumeMaxPermissions(sCurr, h, id, args, toLose, vCurr)

      visitedHeaps = h1 :: visitedHeaps

      assert(consumedChunks(hs.length - 1 - heapsToVisit.length).isEmpty)
      consumedChunks(hs.length - 1 - heapsToVisit.length) = optCh1
      toLose = toLose1
      sCurr = s1
      vCurr = v1
    }

    if (vCurr.decider.check(IsNonPositive(toLose), Verifier.config.checkTimeout())) {
      val tEqs =
        consumedChunks.flatten.sliding(2).map {
          case Array(ch1: NonQuantifiedChunk, ch2: NonQuantifiedChunk) => ch1.snap === ch2.snap
          case _ => True()
        }

      vCurr.decider.assume(tEqs.toIterable)

      Q(sCurr, visitedHeaps.reverse ++ heapsToVisit, consumedChunks, vCurr)
    } else
      Failure(pve dueTo InsufficientPermission(locacc)).withLoad(args)
  }

  /* TODO: This is similar, but not as general, as the consumption algorithm
   *       implemented for supporting quantified permissions. It should be
   *       possible to unite the two.
   *
   * TODO: chunkSupporter.findChunk will return the first chunk it finds - and only
   *       the first chunk. That is, if h contains multiple chunks for the
   *       given id, only the first one will be considered. This may result
   *       in missing permissions that could be taken from h.
   */
  private def consumeMaxPermissions(s: State,
                                    h: Heap,
                                    id: ChunkIdentifer,
                                    args: Seq[Term],
                                    pLoss: Term,
                                    v: Verifier)
                                   : (State, Heap, Option[NonQuantifiedChunk], Term, Verifier) = {

    chunkSupporter.findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) =>
        val (pLost, pKeep, pToConsume) =
          if (v.decider.check(PermAtMost(pLoss, ch.perm), Verifier.config.checkTimeout()))
            (pLoss, PermMinus(ch.perm, pLoss), NoPerm())
          else
            (ch.perm, NoPerm(), PermMinus(pLoss, ch.perm))
        val h1 =
          if (v.decider.check(IsNonPositive(pKeep), Verifier.config.checkTimeout())) h - ch
          else h - ch + ch.withPerm(pKeep)
        val consumedChunk = ch.withPerm(pLost)
        (s, h1, Some(consumedChunk), pToConsume, v)

      case None => (s, h, None, pLoss, v)
    }
  }

//  private var cnt = 0L
//  private val packageLogger = LoggerFactory.getLogger("package")

  def packageWand(state: State,
                  wand: ast.MagicWand,
                  proofScript: ast.Seqn,
                  pve: PartialVerificationError,
                  v: Verifier)
                  (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                  : VerificationResult = {

    /* TODO: Logging code is very similar to that in HeuristicsSupporter. Unify. */

//    val myId = cnt; cnt += 1
//    val baseIdent = "  "
//    var printedHeader = false

//    def lnsay(msg: String, ident: Int = 1) {
//      val prefix = "\n" + (if (ident == 0) "" else baseIdent)
//      dosay(prefix, msg, ident - 1)
//    }
//
//    def say(msg: String, ident: Int = 1) {
//      val prefix = if (ident == 0) "" else baseIdent
//      dosay(prefix, msg, ident - 1)
//    }
//
//    def dosay(prefix: String, msg: String, ident: Int) {
//      if (!printedHeader) {
//        packageLogger.debug(s"\n[packageWand $myId]")
//        printedHeader = true
//      }
//
//      val messagePrefix = baseIdent * ident
//      packageLogger.debug(s"$prefix$messagePrefix $msg")
//    }
//
//    say(s"wand = $wand")
//    say("c.reserveHeaps:")
//    s.reserveHeaps.map(v.stateFormatter.format).foreach(str => say(str, 2))

    val s = if (state.exhaleExt) state else
      state.copy(reserveHeaps = Heap() :: state.h :: Nil,
                 recordEffects = true,
                 consumedChunks = Nil :: Nil)

    val stackSize = 3 + s.reserveHeaps.tail.size
      /* IMPORTANT: Size matches structure of reserveHeaps at [State RHS] below */
    var allConsumedChunks: Stack[MMap[Stack[Term], MList[NonQuantifiedChunk]]] = Stack.fill(stackSize - 1)(MMap())
      /* Record consumptions (transfers) from all heaps except the top-most (which is hUsed,
       * from which we never transfer from, only to)
       */
    var finalStates: Seq[State] = Nil
    var magicWandChunk: MagicWandChunk = null

    assert(s.reserveHeaps.head.values.isEmpty)

    /* TODO: When parallelising branches, some of the runtime assertions in the code below crash
     *       during some executions - since such crashes are hard to debug, branch parallelisation
     *       has been disabled for now.
     */
    val sEmp = s.copy(h = Heap(),
                      reserveHeaps = Nil,
                      exhaleExt = false,
                      parallelizeBranches = false)

    var pcsFromHeapIndepExprs = Vector[RecordedPathConditions]()

    val r = executionFlowController.locally(sEmp, v)((s1, v1) => {
      /* Using conservingSnapshotGeneration a snapshot (binary tree) will be
       * constructed using First/Second datatypes, that preserves the original root.
       * The leafs of this tree will later appear in the snapshot of the rhs at the
       * appropriate places. Thus equating freshSnapRoot with the snapshot received
       * from consuming the lhs when applying the wand preserves values from the lhs
       * into the rhs.
       */
      val freshSnapRoot = freshSnap(sorts.Snap, v1)
      produce(s1.copy(conservingSnapshotGeneration = true), toSf(freshSnapRoot), wand.left, pve, v1)((sLhs, v2) => {

        val proofScriptCfg = proofScript.toCfg()

        /* Expected shape of reserveHeaps is either
         *   [hEmp, hOuter]
         * if we are executing a package statement (i.e. if we are coming from the executor), or
         *   [hEmp, hOps, ..., hOuterLHS, hOuter]
         * if we are executing a package ghost operation (i.e. if we are coming from the consumer).
         */
        val s2 = sLhs.copy(g = s.g,
                           h = Heap(),
                           reserveHeaps = Heap() +: Heap() +: sLhs.h +: s.reserveHeaps.tail, /* [State RHS] */
                           reserveCfgs = proofScriptCfg +: sLhs.reserveCfgs,
                           exhaleExt = true,
                           oldHeaps = s.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> sLhs.h),
                           recordEffects = true,
                           conservingSnapshotGeneration = s.conservingSnapshotGeneration,
                           consumedChunks = Stack.fill(stackSize - 1)(Nil))
        /* s2.reserveHeaps is [hUsed, hOps, hLHS, ...], where hUsed and hOps are initially
         * empty, and where the dots represent the heaps belonging to surrounding package/packaging
         * operations. hOps will be populated while processing the RHS of the wand to package.
         * More precisely, each ghost operation (folding, applying, etc.) that is executed
         * populates hUsed (by transferring permissions from heaps lower in the stack, and by
         * adding new chunks, e.g. a folded predicate) during its execution, and afterwards
         * merges hUsed and hOps, the result of which replaces hOps, and hUsed is replaced by a
         * new empty heap (see also the final state updates in, e.g. method `applyingWand`
         * or `unfoldingPredicate` below).
         */
        assert(stackSize == s2.reserveHeaps.length)

//        say(s"done: produced LHS ${wand.left}")
//        say(s"next: consume RHS ${wand.right}")
        executor.exec(s2, proofScriptCfg, v2)((proofScriptState, proofScriptVerifier) => {
          consume(proofScriptState.copy(oldHeaps = s2.oldHeaps, reserveCfgs = proofScriptState.reserveCfgs.tail), wand.right, pve, proofScriptVerifier)((s3, snap, v3) => {
            val s4 = s3.copy(//h = s.h, /* Temporarily */
                             exhaleExt = false,
                             recordEffects = false,
                             oldHeaps = s.oldHeaps,
                             consumedChunks = Stack())

//          say(s"done: consumed RHS ${wand.right}")
//          say(s"next: create wand chunk")
            val preMark = v3.decider.setPathConditionMark()
            magicWandSupporter.createChunk(s4, wand, freshSnapRoot, snap, pve, v3)((s5, ch, v4) => {
//            say(s"done: create wand chunk: $ch")
              pcsFromHeapIndepExprs :+= v4.decider.pcs.after(preMark)
              val mergedSnapshot =
                if (magicWandChunk != null) magicWandChunk.snap.merge(ch.snap, v.decider.pcs.branchConditions)
                else ch.snap
              magicWandChunk = ch.copy(snap = mergedSnapshot)
              /* TODO: Assert that all produced chunks are identical (due to
               * branching, we might get here multiple times per package).
               */

//            lnsay(s"-- reached local end of packageWand $myId --")

//            lnsay(s"s3.consumedChunks:", 2)
//            s3.consumedChunks.foreach(x => say(x.toString(), 3))

              assert(s3.consumedChunks.length <= allConsumedChunks.length)
              /* s3.consumedChunks can have fewer layers due to infeasible execution paths,
               * as illustrated by test case wands/regression/folding_inc1.sil.
               * Hence the at-most comparison.
               */

              val consumedChunks: Stack[MMap[Stack[Term], MList[NonQuantifiedChunk]]] =
                s3.consumedChunks.map(pairs => {
                  val cchs: MMap[Stack[Term], MList[NonQuantifiedChunk]] = MMap()

                  pairs.foreach {
                    case (guards, chunk) => cchs.getOrElseUpdate(guards, MList()) += chunk
                  }

                  cchs
                })

//            say(s"consumedChunks:", 2)
//            consumedChunks.foreach(x => say(x.toString(), 3))

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

//            say(s"allConsumedChunks:", 2)
//            allConsumedChunks.foreach(x => say(x.toString(), 3))

              finalStates :+= s5
              Success()})})})})})

//    cnt -= 1
//    lnsay(s"[end packageWand $myId]")
//
//    say(s"produced magic wand chunk $magicWandChunk")
//    say(s"allConsumedChunks:")
//    allConsumedChunks.foreach(x => say(x.toString(), 2))
//    say(s"recorded ${finalStates.length} final states")
//    finalStates.foreach(s => s.reserveHeaps.map(stateFormatter.format).foreach(str => say(str, 2)))

    r && {
      assert(finalStates.isEmpty == (magicWandChunk == null))

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

        val s1 = s.copy(reserveHeaps = s.reserveHeaps.tail) /* [Remainder reserveHeaps] (match code below) */
        magicWandSupporter.createChunk(s1, wand, pve, v)((s2, ch, v1) => {
//          say(s"done: create wand chunk: $ch")
          Q(s2, ch, v1)})
      } else {
//        lnsay("Restoring path conditions obtained from evaluating heap-independent expressions")
        v.decider.prover.comment("Restoring path conditions obtained from evaluating heap-independent expressions")
        pcsFromHeapIndepExprs.foreach(pcs => v.decider.assume(pcs.asConditionals))

        assert(finalStates.map(_.reserveHeaps).map(_.length).toSet.size == 1)
        val joinedReserveHeaps: Stack[MList[Chunk]] = s.reserveHeaps.tail.map(h => MList() ++ h.values) /* [Remainder reserveHeaps] (match code above) */
        assert(joinedReserveHeaps.length == allConsumedChunks.length - 2)

//        lnsay("Computing joined reserve heaps. Initial stack:")
//        joinedReserveHeaps.foreach(x => say(x.toString(), 2))

        /* Drop the top-most two heaps from the stack, which record the chunks consumed from
         * hOps and hLHS. Chunks consumed from these heaps are irrelevant to the outside
         * package/packaging scope because chunks consumed from
         *   - hOps have either been newly produced during the execution of ghost statements (such as a
         *     predicate obtained by folding it), or they have been transferred into hOps, in which case
         *     they've already been recorded as being consumed from another heap (lower in the stack).
         *   - hLHS is discarded after the packaging is done
         */
        allConsumedChunks = allConsumedChunks.drop(2) /* TODO: Don't record irrelevant chunks in the first place */
        assert(allConsumedChunks.length == joinedReserveHeaps.length)

//        lnsay("Matching joined reserve heaps (as shown) with consumed chunks minus top two layers:")
//        allConsumedChunks.foreach(x => say(x.toString(), 2))

        joinedReserveHeaps.zip(allConsumedChunks).foreach { case (hR, allcchs) =>
          allcchs.foreach { case (guards, chunks) =>
            chunks.foreach(ch => {
              val pLoss = Ite(And(guards), ch.perm, NoPerm())
              var matched = false

              hR.transform {
                case ch1: NonQuantifiedChunk if ch1.args == ch.args && ch1.id == ch.id =>
                  matched = true
                  ch.withPerm(PermMinus(ch1.perm, pLoss))
                case ch1 => ch1
              }

              if (!matched) {
//                lnsay(s"Couldn't find a match for $ch!")
//                say(s"hR = $hR", 2)
//                say(s"guards = $guards", 2)
//                say(s"chunks = $chunks", 2)
                sys.error(s"Could not find a match for the following chunk: $ch")
              }
            })
        }}

//        lnsay("Finished joined reserve heaps. Final stack:")
//        joinedReserveHeaps.foreach(x => say(x.toString(), 2))

        assert(allConsumedChunks.length == s.consumedChunks.length)
        val consumedChunks: Stack[Seq[(Stack[Term], NonQuantifiedChunk)]] =
          allConsumedChunks.zip(s.consumedChunks).map { case (allcchs, cchs) =>
            cchs ++ allcchs.toSeq.flatMap { case (guards, chunks) => chunks.map(ch => (guards, ch))}}

//        lnsay(s"Exiting packageWand $myId. Final consumedChunks:")
//        consumedChunks.foreach(x => say(x.toString(), 2))


        /* TODO: Shouldn't we merge the final states here (modulo certain components)?
         *       Use State.preserveAfterLocalEvaluation?
         */
        val s1 = finalStates.head.copy(reserveHeaps = joinedReserveHeaps.map(Heap(_)),
                                       recordEffects = s.recordEffects,
                                       consumedChunks = consumedChunks,
                                       parallelizeBranches = s.parallelizeBranches /* See comment above */
                                       /*branchConditions = c.branchConditions*/)

        Q(s1, magicWandChunk, v)
      }
    }
  }

  def applyWand(s: State,
                wand: ast.MagicWand,
                pve: PartialVerificationError,
                v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult = {
        consume(s, wand, pve, v)((s1, snap, v1) => {
          val wandSnap = snap.asInstanceOf[MagicWandSnapshot]
          consume(s1, wand.left, pve, v1)((s2, snap, v2) => {
            /* It is assumed that snap and wandSnap.abstractLhs are structurally the same.
             * Since a wand can only be applied once, equating the two snapshots is sound.
             */
            assert(snap.sort == sorts.Snap, s"expected snapshot but found: $snap")
            v2.decider.assume(snap === wandSnap.abstractLhs)
            val s3 = s2.copy(oldHeaps = s1.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> magicWandSupporter.getEvalHeap(s1)))
            produce(s3.copy(conservingSnapshotGeneration = true), toSf(wandSnap.rhsSnapshot), wand.right, pve, v2)((s4, v3) => {
              val s5 = s4.copy(g = s1.g, conservingSnapshotGeneration = s3.conservingSnapshotGeneration)
              val s6 = stateConsolidator.consolidate(s5, v3).copy(oldHeaps = s1.oldHeaps)
              Q(s6, v3)})})})}

  def transfer(s: State,
               id: ChunkIdentifer,
               args: Seq[Term],
               perms: Term,
               locacc: ast.LocationAccess,
               pve: PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[NonQuantifiedChunk], Verifier) => VerificationResult)
              : VerificationResult = {

    assert(s.consumedChunks.length == s.reserveHeaps.tail.length)

    magicWandSupporter.consumeFromMultipleHeaps(s, s.reserveHeaps.tail, id, args, perms, locacc, pve, v)((s1, hs, chs, v1 /*, pcr*/) => {
      val s2 = s1.copy(reserveHeaps = s.reserveHeaps.head +: hs)

      val s3 =
        if (s2.recordEffects) {
          assert(chs.length == s2.consumedChunks.length)
          val bcs = v1.decider.pcs.branchConditions
          val consumedChunks3 =
            chs.zip(s2.consumedChunks).foldLeft(Stack[Seq[(Stack[Term], NonQuantifiedChunk)]]()) {
              case (accConsumedChunks, (optCh, consumed)) =>
                optCh match {
                  case Some(ch) => ((bcs -> ch) +: consumed) :: accConsumedChunks
                  case None => consumed :: accConsumedChunks
                }
            }.reverse

          s2.copy(consumedChunks = consumedChunks3)
        } else
          s2

      val usedChunks = chs.flatten
      val hUsed = stateConsolidator.merge(s3.reserveHeaps.head, Heap(usedChunks), v1)

      val s4 = s3.copy(reserveHeaps = hUsed +: s3.reserveHeaps.tail)

      /* Returning any of the usedChunks should be fine w.r.t to the snapshot
       * of the chunk, since consumeFromMultipleHeaps should have equated the
       * snapshots of all usedChunks.
       */
      Q(s4, usedChunks.headOption, v1)})
  }

  def getEvalHeap(s: State): Heap = {
    if (s.exhaleExt) {
      /* s.reserveHeaps = [hUsed, hOps, sLhs, ...]
       * After a proof script statement such as fold has been executed, hUsed is empty and
       * hOps contains the chunks that were either transferred or newly produced by
       * the statement. Evaluating an expression, e.g. predicate arguments of
       * a subsequent fold, thus potentially requires chunks from hOps.
       * Such an expression should also be able to rely on permissions gained from the lhs
       * of the wand, i.e. chunks in sLhs.
       * On the other hand, once the innermost assertion of the RHS of a wand is
       * reached, permissions are transferred to hUsed, and expressions of the innermost
       * assertion therefore potentially require chunks from hUsed.
       * Since innermost assertions must be self-framing, combining hUsed, hOps and hLhs
       * is sound.
       */
      s.reserveHeaps.head + s.reserveHeaps(1) + s.reserveHeaps(2)
    } else
      s.h
  }

  def getExecutionHeap(s: State): Heap =
    if (s.exhaleExt) s.reserveHeaps.head
    else s.h

  def moveToReserveHeap(newState: State, v: Verifier): State =
    if (newState.exhaleExt) {
      /* newState.reserveHeaps = [hUsed, hOps, ...]
       * During execution permissions are consumed or transferred from hOps and new
       * ones are generated onto the state's heap. E.g. for a fold the body of a predicate
       * is consumed from hOps and permissions for the predicate are added to the state's
       * heap. After a statement is executed those permissions are transferred to hOps.
       */
      val hOpsJoinUsed = stateConsolidator.merge(newState.reserveHeaps(1), newState.h, v)
      newState.copy(h = Heap(),
          reserveHeaps = Heap() +: hOpsJoinUsed +: newState.reserveHeaps.drop(2))
    } else newState

  def getOutEdges(s: State, b: SilverBlock): Seq[Edge[Stmt, Exp]] =
    if (s.exhaleExt)
      s.reserveCfgs.head.outEdges(b)
    else
      s.methodCfg.outEdges(b)
}
