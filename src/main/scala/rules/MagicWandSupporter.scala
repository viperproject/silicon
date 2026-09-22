// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon._
import viper.silicon.decider.{Mark, RecordedPathConditions}
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.resources.MagicWandID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.sorts.{PredHeapSort, WandHeapSort}
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.ast.{Exp, Stmt}
import viper.silver.cfg.Edge
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.parser.PUnknown
import viper.silver.verifier.PartialVerificationError

object magicWandSupporter extends SymbolicExecutionRules {
  import consumer._
  import evaluator._
  import producer._

//  def checkWandsAreSelfFraming(s: State, g: Store, oldHeap: Heap, root: ast.Member, v: Verifier): VerificationResult =
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

  /**
   * Evaluate the wand's arguments and create a [[viper.silicon.state.MagicWandChunk]] out of it.
   */
  def createChunk(s: State,
                  wand: ast.MagicWand,
                  snap: MagicWandSnapshot,
                  pve: PartialVerificationError,
                  v: Verifier)
                 (Q: (State, MagicWandChunk, Verifier) => VerificationResult)
                 : VerificationResult = {
    evaluateWandArguments(s, wand, pve, v)((s1, ts, esNew, v1) =>
      Q(s1, MagicWandChunk(MagicWandIdentifier(wand, s.program), s1.g.values, ts, esNew, snap, FullPerm,
        Option.when(debugOn)(ast.FullPerm()(wand.pos, wand.info, wand.errT)), None), v1)
    )
  }

  /**
   * Evaluate all expressions inside the given magic wand instance in the current state.
   *
   * @param s State in which to expressions are evaluated.
   * @param wand Magic Wand instance.
   * @param Q Method whose second argument is used to return the evaluated terms of all expressions.
   */
  def evaluateWandArguments(s: State,
                            wand: ast.MagicWand,
                            pve: PartialVerificationError,
                            v: Verifier)
                           (Q: (State, Seq[Term], Option[Seq[ast.Exp]], Verifier) => VerificationResult)
                           : VerificationResult = {
    val s1 = s.copy(exhaleExt = false)
    val es = wand.subexpressionsToEvaluate(s.program)

    evals(s1, es, _ => pve, v)((s2, ts, esNew, v1) => {
      Q(s2.copy(exhaleExt = s.exhaleExt), ts, esNew, v1)
    })
  }

  def consumeFromMultipleHeaps[CH <: Chunk]
                              (s: State,
                               hs: Stack[Heap],
                               pLoss: Term,
                               pLossExp: Option[ast.Exp],
                               failure: Failure,
                               qvars: Seq[Var],
                               v: Verifier)
                              (consumeFunction: (State, Heap, Term, Option[ast.Exp], Verifier) => (ConsumptionResult, State, Heap, Option[CH]))
                              (Q: (State, Stack[Heap], Stack[Option[CH]], Verifier) => VerificationResult)
                              : VerificationResult = {

    val initialConsumptionResult = ConsumptionResult(pLoss, pLossExp, qvars, v, Verifier.config.checkTimeout())
      /* TODO: Introduce a dedicated timeout for the permission check performed by ConsumptionResult,
       *       instead of using checkTimeout. Reason: checkTimeout is intended for checks that are
       *       optimisations, e.g. detecting if a chunk provided no permissions or if a branch is
       *       infeasible. The situation is somewhat different here: the check should be time-bounded
       *       because not all permissions need to come from this stack, but the bound should be
       *       (significantly) higher to reduce the chances of missing a chunk that can provide
       *       permissions.
       */
    val initial = (initialConsumptionResult, s, Stack.empty[Heap], Stack.empty[Option[CH]])
    val (result, s1, heaps, consumedChunks) =
      hs.foldLeft[(ConsumptionResult, State, Stack[Heap], Stack[Option[CH]])](initial)((partialResult, heap) =>
        partialResult match {
          case (r: Complete, sIn, hps, cchs)  => (r, sIn, heap +: hps, None +: cchs)
          case (Incomplete(permsNeeded, permsNeededExp), sIn, hps, cchs) =>
            val (success, sOut, h, cch) = consumeFunction(sIn, heap, permsNeeded, permsNeededExp, v)
            /* The snapshots of the chunks consumed from different heaps are equated. For non-quantified chunks,
             * the equality is guarded by the chunks being for the same location (which was established when
             * consuming) with positive permissions, and recorded as a definition: as such, it also holds
             * outside of the current package operation, in particular in the surrounding one.
             */
            val tEq = (cchs.flatten.lastOption, cch) match {
              /* Equating wand snapshots would indirectly equate the actual left hand sides when they are applied
               * and thus be unsound. Since fractional wands do not exist it is not necessary to equate their
               * snapshots. Also have a look at the comments in the packageWand and applyWand methods.
               */
              case (Some(_: MagicWandChunk | _: QuantifiedMagicWandChunk), Some(_: MagicWandChunk | _: QuantifiedMagicWandChunk)) => True
              case (Some(ch1: NonQuantifiedChunk), Some(ch2: NonQuantifiedChunk)) =>
                val sameLocation = And(ch1.args.zip(ch2.args).map({ case (a1, a2) => a1 === a2 }))
                Implies(And(sameLocation, IsPositive(ch1.perm), IsPositive(ch2.perm)), ch1.snap === ch2.snap)
              case (Some(ch1: QuantifiedBasicChunk), Some(ch2: QuantifiedBasicChunk)) => ch1.snapshotMap === ch2.snapshotMap
              case _ => True
            }
            v.decider.assumeDefinition(tEq, Option.when(debugOn)(DebugExp.createInstance("Snapshots", isInternal_ = true)))

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
      case Incomplete(_, _) => failure
    }
  }

  /**
   * Package a magic wand into a chunk. It performs the computation of the wand's footprint
   * and captures all values associated to these locations inside the wand's snapshot.
   *
   * {{{
   * package A --* B { <proofScript> }
   * }}}
   *
   * For reference see Chapter 3 and 5 of [[http://malte.schwerhoff.de/docs/phd_thesis.pdf Malte Schwerhoff's PhD thesis]]
   * and [[https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Nils_Becker_BA_report.pdf Nils Becker's Bachelor report]]
   *
   * The wand's snapshot is a fresh magic wand snap function (MWSF) `mwsf`, which maps snapshots of the
   * wand's LHS to snapshots of its RHS. Packaging a wand may branch (e.g. on the values of the LHS), and
   * each branch may define `mwsf` differently and result in a different state. Therefore:
   *   - The states of all branches are merged into a single state, where the branch conditions that depend
   *     on the LHS are replaced by conditions on unknown snapshots (see below).
   *   - The branch and path conditions of each branch (including the definition of `mwsf`), quantified
   *     over the LHS snapshot, are guarded by the wand's token, i.e. it is assumed that
   *     {{{
   *     forall lhs :: MW_token(mwsf, lhs) ==> (bcs_1(lhs) && pcs_1(lhs)) || ... || (bcs_n(lhs) && pcs_n(lhs))
   *     }}}
   *     Applying the wand yields the token for the snapshot of the consumed LHS (see [[applyWand]]),
   *     which makes these path conditions available.
   *
   * @param state Current state.
   * @param wand AST representation of the magic wand.
   * @param proofScript AST of the proof script. The proof script contains instructions how we can construct the RHS given the LHS.
   * @param pve Partial Verification Error that is used to report errors.
   * @param v Verifier instance.
   * @param Q Continuation-style function that is called with the resulting state and the chunk that was created.
   * @return Result of the overall verification process.
   */
  def packageWand(state: State,
                  wand: ast.MagicWand,
                  proofScript: ast.Seqn,
                  pve: PartialVerificationError,
                  v: Verifier)
                 (Q: (State, Chunk, Verifier) => VerificationResult)
                 : VerificationResult = {

    /* The heaps of the surrounding state are not consolidated while packaging the wand (see
     * StateConsolidator), since merging their chunks under the assumptions made while packaging
     * (in particular, those about the wand's LHS) would be unsound. They are therefore consolidated
     * beforehand, such that permissions that are known to alias can be transferred to the wand's footprint.
     */
    val sConsolidated = v.stateConsolidator(state).consolidate(state, v)

    val s = if (sConsolidated.exhaleExt) sConsolidated else
      sConsolidated.copy(reserveHeaps = v.heapSupporter.getEmptyHeap(state.program, v) :: sConsolidated.h :: Nil)

    /* The wand's arguments (see MagicWand.subexpressionsToEvaluate) do not depend on the current heap,
     * and thus not on the wand's LHS. They are evaluated upfront, in the current state, such that the
     * path conditions resulting from their evaluation are not scoped to the package operation.
     */
    evals(s, wand.subexpressionsToEvaluate(s.program), _ => pve, v)((s1, tArgs, eArgs, v1) =>
      packageWandWithArguments(s1, wand, tArgs, eArgs, proofScript, pve, v1)(Q))
  }

  private def packageWandWithArguments(s: State,
                                       wand: ast.MagicWand,
                                       tArgs: Seq[Term],
                                       eArgs: Option[Seq[ast.Exp]],
                                       proofScript: ast.Seqn,
                                       pve: PartialVerificationError,
                                       v: Verifier)
                                      (Q: (State, Chunk, Verifier) => VerificationResult)
                                      : VerificationResult = {

    val stackSize = 3 + s.reserveHeaps.tail.size
    // IMPORTANT: Size matches structure of reserveHeaps at [State RHS] below

    /* A snapshot (binary tree) will be constructed using First/Second datatypes,
     * that preserves the original root. The leafs of this tree will later appear
     * in the snapshot of the RHS at the appropriate places. Thus applying the wand's
     * MWSF to the snapshot received from consuming the LHS when applying the wand
     * preserves values from the LHS into the RHS.
     * The snapshot root and the MWSF are shared by all branches of the package operation.
     */
    val freshSnapRoot = freshSnap(sorts.Snap, v)
    val mwsf = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction, Option.when(debugOn)(PUnknown()))
    val wandSnapshot = MagicWandSnapshot(mwsf)

    /* The final state of each branch of the package operation, together with the branch and path
     * conditions recorded on that branch (relative to the beginning of the package operation).
     */
    var recordedBranches: Seq[(State, RecordedPathConditions)] = Nil

    /* TODO: When parallelising branches, some of the runtime assertions in the code below crash
     *       during some executions - since such crashes are hard to debug, branch parallelisation
     *       has been disabled for now.
     */
    val sEmp = s.copy(h = v.heapSupporter.getEmptyHeap(s.program, v),
                      reserveHeaps = Nil,
                      exhaleExt = false,
                      parallelizeBranches = false)

    def defineSnapshotAndRecordBranch(s5: State, snapRhs: Term, packageMark: Mark, v5: Verifier): VerificationResult = {
      v5.decider.prover.comment(s"Define MagicWandSnapFunction for wand $wand on the current branch")
      v5.decider.assumeDefinition(wandSnapshot.applyToMWSF(freshSnapRoot) === snapRhs,
                                  Option.when(debugOn)(DebugExp.createInstance("Magic wand snapshot definition", true)))

      val s6 = s5.copy(packagingWandSnapshots = s5.packagingWandSnapshots.filterNot(_._1 == freshSnapRoot),
                       parallelizeBranches = s.parallelizeBranches /* See comment above */)

      recordedBranches :+= (s6, v5.decider.pcs.after(packageMark))

      Success()
    }

    val tempResult = executionFlowController.locally(sEmp, v)((s1, v1) => {
      val packageMark = v1.decider.setPathConditionMark()

      // Record the abstract LHS snapshot so that new declarations created while packaging are parameterized by it
      // (see State.packagingWandSnapshots); each apply of the resulting wand then gets its own LHS snapshot.
      val freshSnapshotRootVar = Option.when(debugOn)(ast.LocalVar("LHS", ast.InternalType)())
      val s1WithSnapRoot = s1.copy(packagingWandSnapshots = (freshSnapRoot, freshSnapshotRootVar) +: s1.packagingWandSnapshots)

      // Produce the wand's LHS.
      produce(s1WithSnapRoot.copy(conservingSnapshotGeneration = true), toSf(freshSnapRoot), wand.left, pve, v1)((sLhs, v2) => {
        val proofScriptCfg = proofScript.toCfg()
        val emptyHeap = v2.heapSupporter.getEmptyHeap(sLhs.program, v2)

        /* Expected shape of reserveHeaps is either
         *   [hEmp, hOuter]
         * if we are executing a package statement (i.e. if we are coming from the executor), or
         *   [hEmp, hOps, ..., hOuterLHS, hOuter]
         * if we are executing a package ghost operation (i.e. if we are coming from the consumer).
         */
        val s2 = sLhs.copy(g = s.g, // TODO: s1.g? And analogously, s1 instead of s further down?
                           h = emptyHeap,
                           reserveHeaps = emptyHeap +: emptyHeap +: sLhs.h +: s.reserveHeaps.tail, /* [State RHS] */
                           reserveCfgs = proofScriptCfg +: sLhs.reserveCfgs,
                           exhaleExt = true,
                           oldHeaps = s.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> sLhs.h),
                           conservingSnapshotGeneration = s.conservingSnapshotGeneration)
        /* s2.reserveHeaps is [hUsed, hOps, hLHS, ...], where hUsed and hOps are initially
         * empty, and where the dots represent the heaps belonging to surrounding package/packaging
         * operations. hOps will be populated while processing the RHS of the wand to package.
         * More precisely, each ghost operation (folding, applying, etc.) that is executed
         * populates hUsed during its execution. This is done by transferring permissions
         * from heaps lower in the stack, and by adding new chunks, e.g. a folded predicate.
         * Afterwards, it merges hUsed and hOps, which replaces hOps. hUsed is replaced by a
         * new empty heap. See also the final state updates in, e.g. method `applyingWand`
         * or `unfoldingPredicate` below.
         */
        assert(stackSize == s2.reserveHeaps.length)

        // Execute proof script, i.e. the part written after the magic wand wrapped by curly braces.
        // The proof script should transform the current state such that we can consume the wand's RHS.
        executor.exec(s2, proofScriptCfg, v2)((proofScriptState, proofScriptVerifier) => {
          // Consume the wand's RHS and produce a snapshot which records all the values of variables on the RHS.
          // This part indirectly calls the methods `this.transfer` and `this.consumeFromMultipleHeaps`.
          consume(
            proofScriptState.copy(oldHeaps = s2.oldHeaps, reserveCfgs = proofScriptState.reserveCfgs.tail),
            wand.right, true, pve, proofScriptVerifier
          )((s3, snapRhs, v3) => {

            defineSnapshotAndRecordBranch(s3.copy(exhaleExt = false, oldHeaps = s.oldHeaps), snapRhs.get, packageMark, v3)
          })
        })
      })
    })

    val sJoined =
      if (recordedBranches.isEmpty) {
        // No results mean that packaging the wand resulted in inconsistent states on all paths,
        // and thus, that no wand chunk was created. In order to continue, we create one now, whose
        // snapshot function remains unconstrained.
        // Moreover, we need to set reserveHeaps to structurally match [State RHS] below.
        val emptyHeap = v.heapSupporter.getEmptyHeap(sEmp.program, v)
        sEmp.copy(reserveHeaps = emptyHeap +: emptyHeap +: emptyHeap +: s.reserveHeaps.tail,
                  parallelizeBranches = s.parallelizeBranches)
      } else {
        /* Merge the states of all branches into a single state, in which the heaps (and the store) are
         * conditionalised by the branch conditions.
         *
         * Branch conditions that depend on the LHS, i.e. on freshSnapRoot, refer to the hypothetical LHS
         * that was assumed while packaging the wand. After the package operation, freshSnapRoot is an
         * unconstrained constant, and chunks that only exist on some branches remain guarded by
         * conditions on it. E.g. for
         *   package acc(x.b) --* (x.b ? acc(x.f) : acc(x.g))
         * x.g remains available under the condition that the hypothetical LHS's x.b holds, and x.f
         * under the condition that it does not. Neither can be used directly, but once the wand is
         * applied and e.g. acc(x.f) is produced, permission constraints imply that the hypothetical
         * LHS's x.b holds, and thus that x.g is available (cf. wands/examples_paper/conditionals.vpr).
         */
        val branchesToMerge = recordedBranches.map({ case (sBranch, pcs) =>
          val condition = And(pcs.branchConditions)
          val conditionExp = Option.when(debugOn)(BigAnd(pcs.branchConditionExps.map(_._2.get)))
          (sBranch, condition, conditionExp)
        })

        val (sMerged, _, _) =
          branchesToMerge.tail.foldLeft(branchesToMerge.head)({ case ((sAcc, condAcc, condAccExp), (sBranch, cond, condExp)) =>
            (State.merge(sAcc, condAcc, condAccExp, sBranch, cond, condExp),
             Or(condAcc, cond),
             condAccExp.map(cae => ast.Or(cae, condExp.get)()))
          })

        /* The branch and path conditions recorded on each branch, including the definition of the
         * wand's MWSF for that branch, are only known to hold for the LHS the branch was taken for.
         * They are therefore quantified over the LHS snapshot and guarded by the wand's token, which
         * is yielded for the actual LHS snapshot when the wand is applied.
         */
        val branchConditions = recordedBranches.map({ case (_, pcs) => And(pcs.branchConditions ++ pcs.conditionalized) })
        val token = wandSnapshot.yieldToken(freshSnapRoot)
        val tokenAxiom = Forall(freshSnapRoot, Implies(token, Or(branchConditions)), Trigger(token))
        v.decider.prover.comment(s"Path conditions recorded while packaging wand $wand, guarded by the wand's token")
        v.decider.assume(tokenAxiom, Option.when(debugOn)(DebugExp.createInstance("Path conditions recorded while packaging the magic wand", tokenAxiom, true)))

        /* Producing the wand's LHS and executing the proof script can introduce definitional path
         * conditions, e.g. definitions of new snapshot and permission maps (see Decider.assumeDefinition),
         * which are in general necessary to proceed after the package operation, e.g. to know which
         * permissions have been consumed from the surrounding heaps. Definitions that do not depend on
         * the LHS are therefore kept (as definitions, such that a surrounding package operation keeps
         * them as well); the others are available through the wand's token.
         */
        val definitions =
          recordedBranches.flatMap({ case (_, pcs) => pcs.definingAssumptions })
                          .distinct
                          .filterNot(_.contains(freshSnapRoot))
        v.decider.prover.comment(s"Definitions recorded while packaging wand $wand")
        v.decider.assumeDefinition(definitions, Option.when(debugOn)(DebugExp.createInstance("Definitions recorded while packaging the magic wand", true)))

        /* Merging the states of several branches results in several chunks for the same location, each guarded
         * by the corresponding branch condition. Consuming from such heaps is incomplete (in particular, the
         * greedy consumption strategy only takes permissions from one chunk per heap), so the merged state is
         * consolidated, as is done when joining branches elsewhere (see JoinDataEntry.pathConditionAwareMerge).
         */
        if (recordedBranches.length > 1) v.stateConsolidator(sMerged).consolidate(sMerged, v)
        else sMerged
      }

    val s7 = sJoined.copy(reserveHeaps = sJoined.reserveHeaps.drop(3))
    // Ground definitions (e.g. of a quantified wand's snapshot map) are assumed in the current scope by createWandChunk.
    val (chWand, _, _) = v.heapSupporter.createWandChunk(s7, wand, tArgs, eArgs, wandSnapshot, v)

    tempResult combine Q(s7, chWand, v)
  }

  /**
   * Apply a magic wand to the current state. This consumes the magic wand itself and the LHS of the wand, and then produces the RHS.
   *
   * @param s Current state.
   * @param wand The AST instance of the magic wand to apply.
   * @param pve Partial Verification Error that is used to report errors.
   * @param v Verifier instance.
   * @param Q Continuation-style function that is called with the resulting state and the verification result.
   * @return Result of the overall verification process.
   */
  def applyWand(s: State,
                wand: ast.MagicWand,
                pve: PartialVerificationError,
                v: Verifier)
               (Q: (State, Verifier) => VerificationResult)
               : VerificationResult = {
    // Consume the magic wand instance "A --* B".
    consume(s, wand, true, pve, v)((s1, snapWand, v1) => {
      // Consume the wand's LHS "A".
      consume(s1, wand.left, true, pve, v1)((s2, snapLhs, v2) => {
        /* It is assumed that snap and MagicWandSnapshot.abstractLhs are structurally the same.
         * Equating the two snapshots is sound iff a wand is applied only once.
         * The old solution in this case did use this assumption:
         * v2.decider.assume(snap === snapWand.abstractLhs)
         */
        assert(snapLhs.get.sort == sorts.Snap, s"expected snapshot but found: $snapLhs")

        // Create copy of the state with a new labelled heap (i.e. `oldHeaps`) called "lhs".
        val s3 = s2.copy(oldHeaps = s1.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> this.getEvalHeap(s1, v2)))

        // Look up the RHS snapshot by applying snapLhs to the wand's MWSF (a (wrapped)
        // MagicWandSnapshot for an individual wand, or an MWSF-sorted lookup for a quantified one).
        val magicWandSnapshotLookup =
          v2.heapSupporter.appliedWandSnapshot(snapWand.get, snapLhs.get, s2, v2)

        // Yield the wand's token for the consumed LHS. This makes the path conditions that were recorded
        // while packaging the wand (in particular, the definition of its MWSF) available, see packageWand.
        magicWandSnapshotLookup match {
          case MWSFLookup(mwsfTerm, _) =>
            v2.decider.assume(MagicWandToken(mwsfTerm, snapLhs.get),
                              Option.when(debugOn)(DebugExp.createInstance("Magic wand token", true)))
          case _ =>
        }

        // Produce the wand's RHS.
        produce(s3.copy(conservingSnapshotGeneration = true), toSf(magicWandSnapshotLookup), wand.right, pve, v2)((s4, v3) => {
          // Recreate old state without the magic wand, and the state with the oldHeap called lhs.
          val s5 = s4.copy(g = s1.g, conservingSnapshotGeneration = s3.conservingSnapshotGeneration)

          // Consolidate the state and remove labelled old heap "lhs".
          val s6 = v3.stateConsolidator(s5).consolidate(s5, v3).copy(oldHeaps = s1.oldHeaps)

          Q(s6, v3)
        })
      })
    })
  }

  def transfer[CH <: Chunk]
              (s: State,
               perms: Term,
               permsExp: Option[ast.Exp],
               failure: Failure,
               qvars: Seq[Var],
               v: Verifier)
              (consumeFunction: (State, Heap, Term, Option[ast.Exp], Verifier) => (ConsumptionResult, State, Heap, Option[CH]))
              (Q: (State, Seq[CH], Verifier) => VerificationResult)
              : VerificationResult = {
    /* Note that all path conditions added while consuming (e.g. about new snapshots) are recorded by the
     * enclosing package operation, and made available once the packaged wand is applied.
     */
    executionFlowController.tryOrFail2[Stack[Heap], Stack[Option[CH]]](s, v)((s1, v1, QS) =>
      this.consumeFromMultipleHeaps(s1, s1.reserveHeaps.tail, perms, permsExp, failure, qvars, v1)(consumeFunction)(QS)
    )((s2, hs2, chs2, v2) => {
      val s3 = s2.copy(reserveHeaps = s.reserveHeaps.head +: hs2)

      val usedChunks = chs2.flatten
      val (fr4, hUsed) = v2.heapSupporter.mergeTransferredChunks(s3.functionRecorder, s2, s2.reserveHeaps.head, usedChunks, v2)

      val s4 = s3.copy(functionRecorder = fr4, reserveHeaps = hUsed +: s3.reserveHeaps.tail)

      /* All consumed chunks are returned. For the default chunk formats, using any of
       * them (conventionally the last) is fine w.r.t. the snapshot of the chunk, since
       * consumeFromMultipleHeaps equates the snapshots of all usedChunks; the exception
       * are magic wand chunks, where usedChunks is potentially a series of empty chunks
       * (perm = Z) followed by the one that was actually consumed. Chunk formats whose
       * consumed chunks record the taken amounts (e.g. mask/heap chunks) must combine
       * all chunks, since the permissions may have been taken from several heaps.
       */
      Q(s4, usedChunks, v2)})
  }

  def getEvalHeap(s: State, v: Verifier): Heap = {
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
      v.heapSupporter.mergeReserveHeaps(s.reserveHeaps.head, s.reserveHeaps(1), s.reserveHeaps(2), s, v)
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
      val emptyHeap = v.heapSupporter.getEmptyHeap(newState.program, v)
      val (fr, hOpsJoinUsed) = v.stateConsolidator(newState).merge(newState.functionRecorder, newState, newState.reserveHeaps(1), newState.h, v)
      newState.copy(functionRecorder = fr, h = emptyHeap,
          reserveHeaps = emptyHeap +: hOpsJoinUsed +: newState.reserveHeaps.drop(2))
    } else newState

  def getOutEdges(s: State, b: SilverBlock): Seq[Edge[Stmt, Exp]] =
    if (s.exhaleExt)
      s.reserveCfgs.head.outEdges(b)
    else
      s.methodCfg.outEdges(b)
}
