/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.ast.{Exp, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.verifier.PartialVerificationError
import viper.silicon._
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.state._
import viper.silicon.state.terms.{MagicWandSnapshot, _}
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier

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
    createChunk(s, wand, MagicWandSnapshot(freshSnap(sorts.Snap, v), freshSnap(sorts.Snap, v)), pve, v)(Q)

  def createChunk(s: State,
                  wand: ast.MagicWand,
                  abstractLhs: Term,
                  rhsSnapshot: Term,
                  pve: PartialVerificationError,
                  v: Verifier)
                  (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                  : VerificationResult =
    createChunk(s, wand, MagicWandSnapshot(abstractLhs, rhsSnapshot), pve, v)(Q)

  def createChunk(s: State,
                  wand: ast.MagicWand,
                  snap: MagicWandSnapshot,
                  pve: PartialVerificationError,
                  v: Verifier)
                 (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                 : VerificationResult = {
    evaluateWandArguments(s, wand, pve, v)((s1, ts, v1) =>
      Q(s1, MagicWandChunk(MagicWandIdentifier(wand, Verifier.program), s1.g.values, ts, snap, FullPerm()), v1)
    )
  }

  def evaluateWandArguments(s: State,
                            wand: ast.MagicWand,
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Seq[Term], Verifier) => VerificationResult)
                           : VerificationResult = {
    val s1 = s.copy(exhaleExt = false)
    val es = wand.subexpressionsToEvaluate(Verifier.program)

    evals(s1, es, _ => pve, v)((s2, ts, v1) => {
      Q(s2.copy(exhaleExt = s.exhaleExt), ts, v1)
    })
  }

  def consumeFromMultipleHeaps[CH <: Chunk]
                              (s: State,
                               hs: Stack[Heap],
                               pLoss: Term,
                               failure: Failure,
                               v: Verifier)
                              (consumeFunction: (State, Heap, Term, Verifier) => (ConsumptionResult, State, Heap, Option[CH]))
                              (Q: (State, Stack[Heap], Stack[Option[CH]], Verifier) => VerificationResult)
                              : VerificationResult = {
    val initial = (ConsumptionResult(pLoss, v), s, Stack.empty[Heap], Stack.empty[Option[CH]])
    val (result, s1, heaps, consumedChunks) =
      hs.foldLeft[(ConsumptionResult, State, Stack[Heap], Stack[Option[CH]])](initial)((partialResult, heap) =>
        partialResult match  {
          case (r: Complete, sIn, hps, cchs)  => (r, sIn, heap +: hps, None +: cchs)
          case (Incomplete(permsNeeded), sIn, hps, cchs) =>
            val (success, sOut, h, cch) = consumeFunction(sIn, heap, permsNeeded, v)
            val tEq = (cchs.flatten.lastOption, cch) match {
              /* Equating wand snapshots would indirectly equate the actual left hand sides when they are applied
               * and thus be unsound. Since fractional wands do not exist it is not necessary to equate their
               * snapshots. Also have a look at the comments in the packageWand and applyWand methods.
               */
              case (Some(_: MagicWandChunk), Some(_: MagicWandChunk)) => True()
              case (Some(ch1: NonQuantifiedChunk), Some(ch2: NonQuantifiedChunk)) => ch1.snap === ch2.snap
              case (Some(ch1: QuantifiedBasicChunk), Some(ch2: QuantifiedBasicChunk)) => ch1.snapshotMap === ch2.snapshotMap
              case _ => True()
            }
            v.decider.assume(tEq)

            /* In the future it might be worth to recheck whether the permissions needed, in the case of
             * success being an instance of Incomplete, are zero.
             * For example if an assertion similar to x.f == 0 ==> acc(x.f) has previously been exhaled, Silicon
             * currently branches and if we learn that x.f != 0 from tEq above one of the branches becomes
             * infeasible. If a future version of Silicon would introduce conditionals to the permission term
             * of the corresponding chunk instead of branching we might get something similar to
             * Incomplete(W - (x.f == 0 ? Z : W)) for success, when using transfer to consume acc(x.f).
             * After learning x.f != 0 we would then be done, which is not detected by a smoke check.
             *
             * Note that when tEq is assumed it should be ensured, that permissions have actually been taken
             * from heap, i.e. that tEq does not result in already having the required permissions before
             * consuming from heap.
             */
            if (v.decider.checkSmoke()) {
              (Complete(), sOut, h +: hps, cch +: cchs)
            } else {
              (success, sOut, h +: hps, cch +: cchs)
            }
        })
    result match {
      case Complete() =>
        assert(heaps.length == hs.length)
        assert(consumedChunks.length == hs.length)
        Q(s1, heaps.reverse, consumedChunks.reverse, v)
      case Incomplete(_) => failure
    }
  }

//  private var cnt = 0L
//  private val packageLogger = LoggerFactory.getLogger("package")

  def packageWand(state: State,
                  wand: ast.MagicWand,
                  proofScript: ast.Seqn,
                  pve: PartialVerificationError,
                  v: Verifier)
                 (Q: (State, Chunk, Verifier) => VerificationResult)
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
    var results: Seq[(State, Stack[Term], Vector[RecordedPathConditions], Chunk)] = Nil

    /* TODO: When parallelising branches, some of the runtime assertions in the code below crash
     *       during some executions - since such crashes are hard to debug, branch parallelisation
     *       has been disabled for now.
     */
    val sEmp = s.copy(h = Heap(),
                      reserveHeaps = Nil,
                      exhaleExt = false,
                      conservedPcs = Vector[RecordedPathConditions]() +: s.conservedPcs,
                      recordPcs = true,
                      parallelizeBranches = false)

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
            if (s4.qpMagicWands.contains(MagicWandIdentifier(wand, Verifier.program))) {
              val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
              val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))
              evals(s4, bodyVars, _ => pve, v3)((s5, args, v4) => {
                val (sm, smValueDef) =
                  quantifiedChunkSupporter.singletonSnapshotMap(s5, wand, args, MagicWandSnapshot(freshSnapRoot, snap), v4)
                v4.decider.prover.comment("Definitional axioms for singleton-SM's value")
                v4.decider.assume(smValueDef)
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, wand, args, FullPerm(), sm)

                val conservedPcs = s5.conservedPcs.head :+ v4.decider.pcs.after(preMark)
                val conservedPcsTail = s5.conservedPcs.tail
                val newConservedPcs =
                  if (conservedPcsTail.isEmpty) conservedPcsTail
                  else {
                    val head = conservedPcsTail.head ++ conservedPcs
                    head +: conservedPcsTail.tail
                  }

                results :+= (s5.copy(conservedPcs = newConservedPcs, recordPcs = s.recordPcs), v4.decider.pcs.branchConditions, conservedPcs, ch)
                Success()
              })
            }
            else magicWandSupporter.createChunk(s4, wand, freshSnapRoot, snap, pve, v3)((s5, ch, v4) => {
//            say(s"done: create wand chunk: $ch")
              val conservedPcs = s5.conservedPcs.head :+ v4.decider.pcs.after(preMark)
              val conservedPcsTail = s5.conservedPcs.tail
              val newConservedPcs =
                if (conservedPcsTail.isEmpty) conservedPcsTail
                else {
                  val head = conservedPcsTail.head ++ conservedPcs
                  head +: conservedPcsTail.tail
                }

              results :+= (s5.copy(conservedPcs = newConservedPcs, recordPcs = s.recordPcs), v4.decider.pcs.branchConditions, conservedPcs, ch)
              Success()
            })})})})})

    results.foldLeft(r)((res, packageOut) => {
      res && {
        val state = packageOut._1
        val branchConditions = packageOut._2
        val conservedPcs = packageOut._3
        val magicWandChunk = packageOut._4
        val s1 = state.copy(reserveHeaps = state.reserveHeaps.drop(3),
          parallelizeBranches = s.parallelizeBranches /* See comment above */
          /*branchConditions = c.branchConditions*/)
        executionFlowController.locally(s1, v)((s2, v1) => {
          v1.decider.setCurrentBranchCondition(And(branchConditions))
          conservedPcs.foreach(pcs => v1.decider.assume(pcs.conditionalized))
          Q(s2, magicWandChunk, v1)})}})
  }

  def applyWand(s: State,
                wand: ast.MagicWand,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Verifier) => VerificationResult)
               : VerificationResult = {
        consume(s, wand, pve, v)((s1, snap, v1) => {
          val wandSnap = MagicWandSnapshot(snap)
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

  def transfer[CH <: Chunk](s: State,
               perms: Term,
               failure: Failure,
               v: Verifier)
              (consumeFunction: (State, Heap, Term, Verifier) => (ConsumptionResult, State, Heap, Option[CH]))
              (Q: (State, Option[CH], Verifier) => VerificationResult)
              : VerificationResult = {
    assert(s.recordPcs)
    /* During state consolidation or the consumption of quantified permissions new chunks with new snapshots
     * might be created, the information about these new snapshots is stored in the path conditions and needs
     * to be preserved after the package operation finishes.
     * It is assumed that only information regarding snapshots is added to the path conditions during the
     * execution of the consumeFunction. If any other assumptions from the wand's lhs or footprint are
     * recorded, this might not be sound! This might especially happen when consumeFromMultipleHeaps is
     * called in an inconsistent state or when transfer results in an inconsistent state. One solution to
     * consider might be to store the conserved path conditions in the wand's chunk and restore them during
     * the apply operation.
     */
    val preMark = v.decider.setPathConditionMark()
    executionFlowController.tryOrFail2[Stack[Heap], Stack[Option[CH]]](s, v)((s1, v1, QS) =>
      magicWandSupporter.consumeFromMultipleHeaps(s1, s1.reserveHeaps.tail, perms, failure, v1)(consumeFunction)(QS)
    )((s2, hs2, chs2, v2) => {
      val conservedPcs = s2.conservedPcs.head :+ v2.decider.pcs.after(preMark)
      val s3 = s2.copy(conservedPcs = conservedPcs +: s2.conservedPcs.tail, reserveHeaps = s.reserveHeaps.head +: hs2)

      val usedChunks = chs2.flatten
      val hUsed = stateConsolidator.merge(s2.reserveHeaps.head, Heap(usedChunks), v2)

      val s4 = s3.copy(reserveHeaps = hUsed +: s3.reserveHeaps.tail)

      /* Returning the last of the usedChunks should be fine w.r.t to the snapshot
       * of the chunk, since consumeFromMultipleHeaps should have equated the
       * snapshots of all usedChunks, except for magic wand chunks, where usedChunks
       * is potentially a series of empty chunks (perm = Z) followed by the that was
       * actually consumed.
       */
      Q(s4, usedChunks.lastOption, v2)})
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
