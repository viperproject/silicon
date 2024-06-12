// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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
import viper.silicon.state.terms._
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier

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
    evaluateWandArguments(s, wand, pve, v)((s1, ts, v1) =>
      Q(s1, MagicWandChunk(MagicWandIdentifier(wand, s.program), s1.g.values, ts, snap, FullPerm), v1)
    )
  }

  /**
   * Create a new [[viper.silicon.state.terms.MagicWandSnapshot]]
   * and add the corresponding [[viper.silicon.state.terms.sorts.MagicWandSnapFunction]] definition to the state.
   *
   * It defines that when we apply the MagicWandSnapFunction to a snapshot `snap`
   * we will get back `rhsSnapshot` that includes the values from that snapshot `snap`.
   *
   * @param abstractLhs The term that represent the snapshot of the consumed left-hand side of the magic wand.
   *                    It is used as a bound variable in a forall quantifier.
   * @param rhsSnapshot The term that integrates the left-hand side in the snapshot that is produced after applying the magic wand.
   * @param v           Verifier instance
   * @return Fresh instance of [[viper.silicon.state.terms.MagicWandSnapshot]]
   */
  def createMagicWandSnapshot(abstractLhs: Var, rhsSnapshot: Term, v: Verifier): MagicWandSnapshot = {
    val mwsf = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction())
    val magicWandSnapshot = MagicWandSnapshot(mwsf)
    v.decider.assumeDefinition(Forall(
      abstractLhs,
      MWSFLookup(mwsf, abstractLhs) === rhsSnapshot,
      Trigger(MWSFLookup(mwsf, abstractLhs))
    ))
    magicWandSnapshot
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
                           (Q: (State, Seq[Term], Verifier) => VerificationResult)
                           : VerificationResult = {
    val s1 = s.copy(exhaleExt = false)
    val es = wand.subexpressionsToEvaluate(s.program)

    evals(s1, es, _ => pve, v)((s2, ts, v1) => {
      Q(s2.copy(exhaleExt = s.exhaleExt), ts, v1)
    })
  }

  def consumeFromMultipleHeaps[CH <: Chunk]
                              (s: State,
                               hs: Stack[Heap],
                               pLoss: Term,
                               failure: Failure,
                               qvars: Seq[Var],
                               v: Verifier)
                              (consumeFunction: (State, Heap, Term, Verifier) => (ConsumptionResult, State, Heap, Option[CH]))
                              (Q: (State, Stack[Heap], Stack[Option[CH]], Verifier) => VerificationResult)
                              : VerificationResult = {

    val initialConsumptionResult = ConsumptionResult(pLoss, qvars, v, Verifier.config.checkTimeout())
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
          case (Incomplete(permsNeeded), sIn, hps, cchs) =>
            val (success, sOut, h, cch) = consumeFunction(sIn, heap, permsNeeded, v)
            val tEq = (cchs.flatten.lastOption, cch) match {
              /* Equating wand snapshots would indirectly equate the actual left hand sides when they are applied
               * and thus be unsound. Since fractional wands do not exist it is not necessary to equate their
               * snapshots. Also have a look at the comments in the packageWand and applyWand methods.
               */
              case (Some(_: MagicWandChunk), Some(_: MagicWandChunk)) => True
              case (Some(ch1: NonQuantifiedChunk), Some(ch2: NonQuantifiedChunk)) => ch1.snap === ch2.snap
              case (Some(ch1: QuantifiedBasicChunk), Some(ch2: QuantifiedBasicChunk)) => ch1.snapshotMap === ch2.snapshotMap
              case _ => True
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

    val s = if (state.exhaleExt) state else
      state.copy(reserveHeaps = Heap() :: state.h :: Nil)

    val stackSize = 3 + s.reserveHeaps.tail.size
    // IMPORTANT: Size matches structure of reserveHeaps at [State RHS] below
    var recordedBranches: Seq[(State, Stack[Term], Stack[Option[Exp]], Vector[Term], Chunk)] = Nil

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

    def appendToResults(s5: State, ch: Chunk, pcs: RecordedPathConditions, conservedPcs: Vector[Term], v4: Verifier): Unit = {
      assert(s5.conservedPcs.nonEmpty, s"Unexpected structure of s5.conservedPcs: ${s5.conservedPcs}")

      var conservedPcsStack: Stack[Vector[RecordedPathConditions]] = s5.conservedPcs

      // Producing a wand's LHS and executing the packaging proof code can introduce definitional path conditions, e.g.
      // new permission and snapshot maps, which are in general necessary to proceed after the
      // package statement, e.g. to know which permissions have been consumed.
      // Here, we want to keep *only* the definitions, but no other path conditions.

      conservedPcsStack =
        s5.conservedPcs.tail match {
          case empty @ Seq() => empty
          case head +: tail => (head ++ (s5.conservedPcs.head :+ pcs.definitionsOnly)) +: tail
        }

      val s6 = s5.copy(conservedPcs = conservedPcsStack, recordPcs = s.recordPcs)

      recordedBranches :+= (s6, v4.decider.pcs.branchConditions, v4.decider.pcs.branchConditionExps, conservedPcs, ch)
    }

    /**
     * Partition path conditions into a set which include the freshSnapRoot and those which do not.
     * Include the path conditions with the freshSnapRoot in the MWSF definition.
     * It also takes care of special cases that include field value functions.
     *
     * @param conservedPcs Vector of path conditions which have been recorded during the execution of the proof script.
     * @param freshSnapRoot Fresh variable that represents the snapshot of the wand's LHS.
     * @param mwsf MagicWandSnapFunction that is used to lookup the snapshot of the wand's RHS.
     * @param snapRhs Snapshot of the wand's RHS.
     * @param v1 Verifier instance.
     * @return Vector of conserved path conditions.
     */
    def summarizeDefinitions(conservedPcs: Vector[RecordedPathConditions],
                             freshSnapRoot: Var,
                             mwsf: Var,
                             snapRhs: Term,
                             v1: Verifier): Vector[Term] = {
      // Map all path conditions to their conditionalized form and flatten the result
      val conditionalizedPcs = conservedPcs.flatMap(_.conditionalized).flatMap {
        case And(terms) => terms
        case term => Vector(term)
      }

      // Partition path conditions into a set which include the freshSnapRoot and those which do not
      var (pcsWithFreshSnapRoot, pcsWithoutFreshSnapRoot) = conditionalizedPcs.partition(pcs => pcs.contains(freshSnapRoot))

      // Remove forall quantifiers with the same quantified variable
      pcsWithFreshSnapRoot = pcsWithFreshSnapRoot
        .map(_.transform {
          case Quantification(Forall, v :: Nil, body: Term, _, _, _, _) if v.equals(freshSnapRoot) => body
        }(_ => true))

      val mwsfLookup = MWSFLookup(mwsf, freshSnapRoot)
      // If the snapRhs is a FieldValueFunction or PredicateSnapFunction, substitute the snapRhs with the MWSFLookup definition
      val updatedPcs = snapRhs match {
        // Rewrite based on test11 in QPFields.vpr
        case SortWrapper(app: App, _) if
          app.applicable.resultSort.isInstanceOf[sorts.FieldValueFunction] ||
            app.applicable.resultSort.isInstanceOf[sorts.PredicateSnapFunction] =>

          def rewriteTerms(r: Var, cond: Term, terms: Iterable[Term]): Vector[Quantification] = {
            val newTerms = terms.filter(_ match {
              case BuiltinEquals(Lookup(_, fvf, at), _) => r.sort == sorts.Ref && fvf == app && r == at
              case BuiltinEquals(PredicateLookup(_, psf, args), _) => r.sort == sorts.Snap && psf == app && args == List(r)
              case _ => false
            }).map {
              case BuiltinEquals(lookup, rhs) =>
                val newLookup = lookup match {
                  case Lookup(field, fvf, at) => Lookup(field, SortWrapper(mwsfLookup, fvf.sort), at)
                  case PredicateLookup(predname, psf, args) => PredicateLookup(predname, SortWrapper(mwsfLookup, psf.sort), args)
                }
                BuiltinEquals(newLookup, rhs)
            }
            if (newTerms.isEmpty) return Vector.empty
            val quantification = Forall(
              Seq(r, freshSnapRoot),
              Implies(cond, And(newTerms)),
              newTerms.map { case BuiltinEquals(lhs, _) => Trigger(lhs) }.toSeq
            )
            v1.decider.assumeDefinition(quantification)
            Vector(quantification)
          }

          conditionalizedPcs.flatMap {
            case Quantification(Forall, Seq(r), Implies(cond, And(terms)), _, _, _, _) => rewriteTerms(r, cond, terms)
            case Quantification(Forall, Seq(r), Implies(cond, term), _, _, _, _) => rewriteTerms(r, cond, Seq(term))
            case _ => Vector.empty
          }

        // Rewrite for test9 in QPFields.vpr
        case SortWrapper(lookup, to) if
          (lookup.isInstanceOf[Lookup] &&
            lookup.asInstanceOf[Lookup].fvf.isInstanceOf[App] &&
            lookup.asInstanceOf[Lookup].fvf.asInstanceOf[App].applicable.resultSort.isInstanceOf[sorts.FieldValueFunction]) ||
            (lookup.isInstanceOf[PredicateLookup] &&
              lookup.asInstanceOf[PredicateLookup].psf.isInstanceOf[App] &&
              lookup.asInstanceOf[PredicateLookup].psf.asInstanceOf[App].applicable.resultSort.isInstanceOf[sorts.PredicateSnapFunction]) =>

          val app = lookup match {
            case Lookup(_, fvf, _) => fvf
            case PredicateLookup(_, psf, _) => psf
          }

          def rewriteTerms(cond: Term, terms: Iterable[Term]): Vector[Quantification] = {
            val newLhs = mwsfLookup
            val newTerms = terms.filter(_ match {
              case BuiltinEquals(Lookup(_, fvf, _), rhs) => fvf == app && rhs.contains(freshSnapRoot)
              case BuiltinEquals(PredicateLookup(_, psf, _), rhs) => psf == app && rhs.contains(freshSnapRoot)
              case _ => false
            }).map(t => {
              val rhs = t match { case BuiltinEquals(_, rhs) => rhs }
              BuiltinEquals(newLhs, SortWrapper(rhs, to))
            })
            if (newTerms.isEmpty) return Vector.empty
            val quantification = Forall(
              Seq(freshSnapRoot),
              Implies(cond, And(newTerms)),
              Trigger(newLhs)
            )
            v1.decider.assumeDefinition(quantification)
            Vector(quantification)
          }

          conditionalizedPcs.flatMap {
            case Implies(cond, And(terms)) => rewriteTerms(cond, terms)
            case Implies(cond, eq: BuiltinEquals) => rewriteTerms(cond, Seq(eq))
            case _ => Vector.empty
          }

        case _ => Vector.empty
      }

      // Combine all path conditions which include the freshSnapRoot
      val pcsQuantified = Forall(
        freshSnapRoot,
        Implies(
          And(pcsWithFreshSnapRoot),
          BuiltinEquals(mwsfLookup, snapRhs),
        ),
        Trigger(mwsfLookup)
      )

      // Add this definition to the path conditions for outer package operations
      v1.decider.assumeDefinition(Forall(
        freshSnapRoot,
        BuiltinEquals(mwsfLookup, snapRhs),
        Trigger(mwsfLookup)
      ))

      // Return the summarized path conditions
      pcsWithoutFreshSnapRoot ++ updatedPcs :+ pcsQuantified
    }

    def createWandChunkAndRecordResults(s4: State,
                                        freshSnapRoot: Var,
                                        snapRhs: Term,
                                        v3: Verifier)
                                       : VerificationResult = {
      val preMark = v3.decider.setPathConditionMark()

      v3.decider.prover.comment(s"Create MagicWandSnapFunction for wand $wand")
      val mwsf = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction())

      // If the wand is used as a quantified resource anywhere in the program
      if (s4.qpMagicWands.contains(MagicWandIdentifier(wand, s.program))) {
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))

        evals(s4, bodyVars, _ => pve, v3)((s5, args, v4) => {
          val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s5, wand, args, SortWrapper(mwsf, sorts.Snap), v4)
          v4.decider.prover.comment("Definitional axioms for singleton-SM's value")
          v4.decider.assumeDefinition(smValueDef)
          val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, wand, args, FullPerm, sm, s.program)

          val conservedPcs = summarizeDefinitions(
            s5.conservedPcs.head :+ v4.decider.pcs.after(preMark).definitionsOnly,
            freshSnapRoot, mwsf, snapRhs, v4)
          appendToResults(s5, ch, v4.decider.pcs.after(preMark), conservedPcs, v4)
          Success()
        })
      } else {
        val wandSnapshot = MagicWandSnapshot(mwsf)
        this.createChunk(s4, wand, wandSnapshot, pve, v3)((s5, ch, v4) => {
          val conservedPcs = summarizeDefinitions(
            s5.conservedPcs.head :+ v4.decider.pcs.after(preMark).definitionsOnly,
            freshSnapRoot, mwsf, snapRhs, v4)
          appendToResults(s5, ch, v4.decider.pcs.after(preMark), conservedPcs, v4)
          Success()
        })
      }
    }

    val tempResult = executionFlowController.locally(sEmp, v)((s1, v1) => {
      /* A snapshot (binary tree) will be constructed using First/Second datatypes,
       * that preserves the original root. The leafs of this tree will later appear
       * in the snapshot of the RHS at the appropriate places. Thus equating
       * `freshSnapRoot` with the snapshot received from consuming the LHS when
       * applying the wand preserves values from the LHS into the RHS.
       */
      val freshSnapRoot = freshSnap(sorts.Snap, v1)

      // Produce the wand's LHS.
      produce(s1.copy(conservingSnapshotGeneration = true), toSf(freshSnapRoot), wand.left, pve, v1)((sLhs, v2) => {
        val proofScriptCfg = proofScript.toCfg()

        /* Expected shape of reserveHeaps is either
         *   [hEmp, hOuter]
         * if we are executing a package statement (i.e. if we are coming from the executor), or
         *   [hEmp, hOps, ..., hOuterLHS, hOuter]
         * if we are executing a package ghost operation (i.e. if we are coming from the consumer).
         */
        val s2 = sLhs.copy(g = s.g, // TODO: s1.g? And analogously, s1 instead of s further down?
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
            wand.right, pve, proofScriptVerifier
          )((s3, snapRhs, v3) => {

            createWandChunkAndRecordResults(s3.copy(exhaleExt = false, oldHeaps = s.oldHeaps), freshSnapRoot, snapRhs, v3)
          })
        })
      })
    })

    if (recordedBranches.isEmpty) {
      // No results mean that packaging the wand resulted in inconsistent states on all paths,
      // and thus, that no wand chunk was created. In order to continue, we create one now.
      // Moreover, we need to set reserveHeaps to structurally match [State RHS] below.
      val s1 = sEmp.copy(reserveHeaps = Heap() +: Heap() +: Heap() +: s.reserveHeaps.tail)
      createWandChunkAndRecordResults(s1, freshSnap(sorts.Snap, v), freshSnap(sorts.Snap, v), v)
    }

    recordedBranches.foldLeft(tempResult)((prevRes, recordedState) => {
      prevRes && {
        val (state, branchConditions, branchConditionsExp, conservedPcs, magicWandChunk) = recordedState
        val s1 = state.copy(
          reserveHeaps = state.reserveHeaps.drop(3),
          parallelizeBranches = s.parallelizeBranches /* See comment above */
        )

        // We execute the continuation Q in a new scope with all branch conditions and all conserved path conditions.
        executionFlowController.locally(s1, v)((s2, v1) => {
          // Set the branch conditions
          v1.decider.setCurrentBranchCondition(And(branchConditions), Some(viper.silicon.utils.ast.BigAnd(branchConditionsExp.flatten)))

          // Recreate all path conditions in the Z3 proof script that we recorded for that branch
          conservedPcs.foreach(pcs => v1.decider.assume(pcs))

          // Execute the continuation Q
          Q(s2, magicWandChunk, v1)
        })
      }
    })
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
    consume(s, wand, pve, v)((s1, snapWand, v1) => {
      // Consume the wand's LHS "A".
      consume(s1, wand.left, pve, v1)((s2, snapLhs, v2) => {
        /* It is assumed that snap and MagicWandSnapshot.abstractLhs are structurally the same.
         * Equating the two snapshots is sound iff a wand is applied only once.
         * The old solution in this case did use this assumption:
         * v2.decider.assume(snap === snapWand.abstractLhs)
         */
        assert(snapLhs.sort == sorts.Snap, s"expected snapshot but found: $snapLhs")

        // Create copy of the state with a new labelled heap (i.e. `oldHeaps`) called "lhs".
        val s3 = s2.copy(oldHeaps = s1.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> this.getEvalHeap(s1)))

        // If the snapWand is a (wrapped) MagicWandSnapshot then lookup the snapshot of the right-hand side by applying snapLhs.
        val magicWandSnapshotLookup = snapWand match {
          case snapshot: MagicWandSnapshot => snapshot.applyToMWSF(snapLhs)
          case SortWrapper(snapshot: MagicWandSnapshot, _) => snapshot.applyToMWSF(snapLhs)
          case predicateLookup: PredicateLookup =>
            MWSFLookup(SortWrapper(predicateLookup, sorts.MagicWandSnapFunction()), snapLhs)
          case SortWrapper(predicateLookup: PredicateLookup, _) =>
            MWSFLookup(SortWrapper(predicateLookup, sorts.MagicWandSnapFunction()), snapLhs)
          case _ => snapWand
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
               failure: Failure,
               qvars: Seq[Var],
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
      this.consumeFromMultipleHeaps(s1, s1.reserveHeaps.tail, perms, failure, qvars, v1)(consumeFunction)(QS)
    )((s2, hs2, chs2, v2) => {
      val conservedPcs = s2.conservedPcs.head :+ v2.decider.pcs.after(preMark)
      val s3 = s2.copy(conservedPcs = conservedPcs +: s2.conservedPcs.tail, reserveHeaps = s.reserveHeaps.head +: hs2)

      val usedChunks = chs2.flatten
      val (fr4, hUsed) = v2.stateConsolidator(s2).merge(s3.functionRecorder, s2.reserveHeaps.head, Heap(usedChunks), v2)

      val s4 = s3.copy(functionRecorder = fr4, reserveHeaps = hUsed +: s3.reserveHeaps.tail)

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
      val (fr, hOpsJoinUsed) = v.stateConsolidator(newState).merge(newState.functionRecorder, newState.reserveHeaps(1), newState.h, v)
      newState.copy(functionRecorder = fr, h = Heap(),
          reserveHeaps = Heap() +: hOpsJoinUsed +: newState.reserveHeaps.drop(2))
    } else newState

  def getOutEdges(s: State, b: SilverBlock): Seq[Edge[Stmt, Exp]] =
    if (s.exhaleExt)
      s.reserveCfgs.head.outEdges(b)
    else
      s.methodCfg.outEdges(b)
}
