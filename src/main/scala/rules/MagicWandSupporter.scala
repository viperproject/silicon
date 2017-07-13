/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon._
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms.perms.IsNonPositive
import viper.silicon.state.terms.{MagicWandSnapshot, _}
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.{Exp, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons.InsufficientPermission

object magicWandSupporter extends SymbolicExecutionRules with Immutable {
  import consumer._
  import evaluator._
  import producer._

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
      Q(s3, MagicWandChunk(wand, s3.g.values, ts, MagicWandSnapshot(snapshotPair._1, snapshotPair._2)), v1)
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

  def consumeFromMultipleHeaps[C <: PermissionChunk](s: State,
                                  hs: Stack[Heap],
                                  pLoss: Term,
                                  failure: Failure,
                                  v: Verifier)
                                 (consumeFunction: (State, Heap, Term, Verifier) => (ConsumptionResult, State, Heap, Option[C]))
                                 (Q: (State, Stack[Heap], Stack[Option[C]], Verifier) => VerificationResult)
                                 : VerificationResult = {
    val (result, s1, heaps, consumedChunks) =
      hs.foldLeft[(ConsumptionResult, State, Stack[Heap], Stack[Option[C]])]((Incomplete(pLoss), s, Stack.empty[Heap], Stack.empty[Option[C]]))((partialResult, heap) =>
        partialResult match  {
          case (Complete(), sIn, heaps, cchs)  => (Complete(), sIn, heap +: heaps, None +: cchs)
          case (Incomplete(permsNeeded), sIn, heaps, cchs) =>
            val (success, sOut, h, cch) = consumeFunction(sIn, heap, permsNeeded, v)
            (success, sOut, h +: heaps, cch +: cchs)
        })
    result match {
      case Complete() =>
        assert(heaps.length == hs.length)
        assert(consumedChunks.length == hs.length)
        val tEqs =
          consumedChunks.flatten.sliding(2).map {
            case Seq(ch1: BasicChunk, ch2: BasicChunk) => ch1.snap === ch2.snap
            case Seq(ch1: QuantifiedChunk, ch2: QuantifiedChunk) => ch1.snapshotMap === ch2.snapshotMap
            case _ => True()
          }
        v.decider.assume(tEqs.toIterable)
        Q(s1, heaps.reverse, consumedChunks.reverse, v)
      case Incomplete(_) => failure
    }
  }

  def consumeFromMultipleHeaps(s: State,
                               hs: Stack[Heap],
                               name: String,
                               args: Seq[Term],
                               pLoss: Term,
                               locacc: ast.LocationAccess,
                               pve: PartialVerificationError,
                               v: Verifier)
                              (Q: (State, Stack[Heap], Stack[Option[BasicChunk]], Verifier) => VerificationResult)
                              : VerificationResult = {

    val consumedChunks: Array[Option[BasicChunk]] = Array.fill(hs.length)(None)
    var toLose = pLoss
    var heapsToVisit = hs
    var visitedHeaps: List[Heap] = Nil
    var sCurr = s
    var vCurr = v

    while (heapsToVisit.nonEmpty && !v.decider.check(IsNonPositive(toLose), Verifier.config.checkTimeout())) {
      val h = heapsToVisit.head
      heapsToVisit = heapsToVisit.tail

      val (s1, h1, optCh1, toLose1, v1) = consumeMaxPermissions(sCurr, h, name, args, toLose, vCurr)

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
          case Array(ch1: BasicChunk, ch2: BasicChunk) => ch1.snap === ch2.snap
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
   * TODO: decider.getChunk will return the first chunk it finds - and only
   *       the first chunk. That is, if h contains multiple chunks for the
   *       given id, only the first one will be considered. This may result
   *       in missing permissions that could be taken from h.
   */
  private def consumeMaxPermissions(s: State,
                                    h: Heap,
                                    name: String,
                                    args: Seq[Term],
                                    pLoss: Term,
                                    v: Verifier)
                                   : (State, Heap, Option[BasicChunk], Term, Verifier) = {

    chunkSupporter.getChunk(h, name, args, v) match {
      case Some(ch) =>
        val (pLost, pKeep, pToConsume) =
          if (v.decider.check(PermAtMost(pLoss, ch.perm), Verifier.config.checkTimeout()))
            (pLoss, PermMinus(ch.perm, pLoss), NoPerm())
          else
            (ch.perm, NoPerm(), PermMinus(pLoss, ch.perm))
        val h1 = h - ch + (ch \ pKeep)
        val consumedChunk = ch \ pLost
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
      state.copy(reserveHeaps = Heap() :: state.h :: Nil)

    val stackSize = 3 + s.reserveHeaps.tail.size
      /* IMPORTANT: Size matches structure of reserveHeaps at [State RHS] below */
    var results: Seq[(State, Stack[Term], MagicWandChunk)] = Nil

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
                           conservingSnapshotGeneration = s.conservingSnapshotGeneration)
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
                             oldHeaps = s.oldHeaps)

//          say(s"done: consumed RHS ${wand.right}")
//          say(s"next: create wand chunk")
            val preMark = v3.decider.setPathConditionMark()
            magicWandSupporter.createChunk(s4, wand, freshSnapRoot, snap, pve, v3)((s5, ch, v4) => {
//            say(s"done: create wand chunk: $ch")
              pcsFromHeapIndepExprs :+= v4.decider.pcs.after(preMark)

              results :+= (s5, v4.decider.pcs.branchConditions, ch)
              Success()
            })})})})})

    v.decider.prover.comment("Restoring path conditions obtained from evaluating heap-independent expressions")
    pcsFromHeapIndepExprs.foreach(pcs => v.decider.assume(pcs.asConditionals))

    results.foldLeft(r)((res, packageOut) => {
      res && {
        val state = packageOut._1
        val branchConditions = packageOut._2
        val magicWandChunk = packageOut._3
        val s1 = state.copy(reserveHeaps = state.reserveHeaps.drop(3),
          parallelizeBranches = s.parallelizeBranches /* See comment above */
          /*branchConditions = c.branchConditions*/)
        executionFlowController.locally(s1, v)((s2, v1) => {
          v1.decider.setCurrentBranchCondition(And(branchConditions))
          Q(s2, magicWandChunk, v1)})}})
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

  def transfer[C <: PermissionChunk](s: State,
               perms: Term,
               failure: Failure,
               v: Verifier)
              (consumeFunction: (State, Heap, Term, Verifier) => (ConsumptionResult, State, Heap, Option[C]))
              (Q: (State, Option[C], Verifier) => VerificationResult)
              : VerificationResult = {

    magicWandSupporter.consumeFromMultipleHeaps(s, s.reserveHeaps.tail, perms, failure, v)(consumeFunction)((s1, hs, chs, v1) => {
      val s2 = s1.copy(reserveHeaps = s.reserveHeaps.head +: hs)

      val usedChunks = chs.flatten
      val hUsed = stateConsolidator.merge(s2.reserveHeaps.head, Heap(usedChunks), v1)

      val s3 = s2.copy(reserveHeaps = hUsed +: s2.reserveHeaps.tail)

      /* Returning any of the usedChunks should be fine w.r.t to the snapshot
       * of the chunk, since consumeFromMultipleHeaps should have equated the
       * snapshots of all usedChunks.
       */
      Q(s3, usedChunks.headOption, v1)})
  }

  def transfer(s: State,
               name: String,
               args: Seq[Term],
               perms: Term,
               locacc: ast.LocationAccess,
               pve: PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[BasicChunk], Verifier) => VerificationResult)
              : VerificationResult = {

    magicWandSupporter.consumeFromMultipleHeaps(s, s.reserveHeaps.tail, name, args, perms, locacc, pve, v)((s1, hs, chs, v1/*, pcr*/) => {
      val s2 = s1.copy(reserveHeaps = s.reserveHeaps.head +: hs)

      val usedChunks = chs.flatten
      val hUsed = stateConsolidator.merge(s2.reserveHeaps.head, Heap(usedChunks), v1)

      val s3 = s2.copy(reserveHeaps = hUsed +: s2.reserveHeaps.tail)

      /* Returning any of the usedChunks should be fine w.r.t to the snapshot
       * of the chunk, since consumeFromMultipleHeaps should have equated the
       * snapshots of all usedChunks.
       */
      Q(s3, usedChunks.headOption, v1)})
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

  def getMatchingChunk(h: Heap, chunk: MagicWandChunk, v: Verifier): Option[MagicWandChunk] = {
    val mwChunks = h.values.collect { case ch: MagicWandChunk => ch }
    mwChunks.find(ch => compareWandChunks(chunk, ch, v))
  }

  private def compareWandChunks(chWand1: MagicWandChunk,
                                chWand2: MagicWandChunk,
                                v: Verifier)
                               : Boolean = {
//    println(s"\n[compareWandChunks]")
//    println(s"  chWand1 = ${chWand1.ghostFreeWand}")
//    println(s"  chWand2 = ${chWand2.ghostFreeWand}")
    var b = chWand1.ghostFreeWand.structurallyMatches(chWand2.ghostFreeWand, Verifier.program)
//    println(s"  after structurallyMatches: b = $b")
    b = b && chWand1.evaluatedTerms.length == chWand2.evaluatedTerms.length
//    println(s"  after comparing evaluatedTerms.length's: b = $b")
    b = b && v.decider.check(And(chWand1.evaluatedTerms zip chWand2.evaluatedTerms map (p => p._1 === p._2)), Verifier.config.checkTimeout())
//    println(s"  after comparing evaluatedTerms: b = $b")

    b
  }
}
