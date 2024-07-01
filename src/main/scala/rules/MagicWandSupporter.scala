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
import viper.silicon.utils.ast.BigAnd
import viper.silicon.utils.{freshSnap, toSf}
import viper.silicon.verifier.Verifier

import scala.annotation.tailrec
import scala.collection.immutable.Map

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
   * Summarize all path conditions and include them in the definition of the MWSF.
   *
   * This method looks for all snapshot maps that were introduced during the packaging of the wand. It then tries
   * to find a single representative snapshot map for each group of equal snapshot maps.
   *
   * Then it breaks up `snapRhs` into a set of equalities such that we can replace all occurrences of a snapshot map
   * by a term that involves the MWSF. The goal is to replace all occurrences of snapshot maps which were introduced
   * during the packaging of the wand and therefore are only temporary objects that won't be used after the packaging.
   *
   * @param recordedPathConditions   Vector of path conditions which have been recorded during the execution of the proof script.
   * @param abstractLhs              Fresh variable that represents the snapshot of the wand's LHS.
   * @param mwsf                     MagicWandSnapFunction that is used to lookup the snapshot of the wand's RHS.
   * @param snapRhs                  Snapshot of the wand's RHS.
   * @param functionsBeforePackaging Set of functions that were present before the packaging of the wand.
   * @param v1                       Verifier instance.
   * @return Set of all path conditions including the MWSF definition.
   */
  private def summarizeDefinitions(recordedPathConditions: Vector[RecordedPathConditions],
                                   abstractLhs: Var,
                                   mwsf: Term,
                                   snapRhs: Term,
                                   functionsBeforePackaging: Set[FunctionDecl],
                                   v1: Verifier): Vector[Term] = {
    val mwsfApply = MWSFApply(mwsf, abstractLhs)

    // Find all snapshot maps that were introduced during the packaging of the wand
    val freshSnapshotMaps = (v1.decider.freshFunctions -- functionsBeforePackaging)
      .filter(f => f.func.resultSort.isInstanceOf[sorts.FieldValueFunction] || f.func.resultSort.isInstanceOf[sorts.PredicateSnapFunction])

    // Map all path conditions to their conditionalized form and flatten the result
    var conditionalizedPcs = recordedPathConditions.flatMap(_.conditionalized).flatMap {
      case And(terms) => terms
      case term => Vector(term)
    }

    // Helper function to find the parent node of a snapshot map in a union-find data structure
    @tailrec def findParentNode(map: Map[String, String], x: String): String = if (map(x) == x) x else findParentNode(map, map(x))

    // Identify groups of equal snapshot maps
    val groups = conditionalizedPcs.collect {
      // Extract names of all FVFs and PSFs that are part of an equality of the form: fvf0 == fvf1 or psf0 == psf1
      case BuiltinEquals(App(fvf0, Seq()), App(fvf1, Seq()))
        if fvf0.resultSort.isInstanceOf[sorts.FieldValueFunction] && fvf1.resultSort.isInstanceOf[sorts.FieldValueFunction]
        => (fvf0.id.name, fvf1.id.name)
      case BuiltinEquals(App(psf0, Seq()), App(psf1, Seq()))
        if psf0.resultSort.isInstanceOf[sorts.PredicateSnapFunction] && psf1.resultSort.isInstanceOf[sorts.PredicateSnapFunction]
        => (psf0.id.name, psf1.id.name)
    }.foldLeft(
      freshSnapshotMaps.map(f => (f.func.id.name, f.func.id.name)).toMap
    )((assignments, eq) => {
      // Find all groups of equal snapshot maps using a union-find data structure
      val (a, b) = eq
      if (!assignments.contains(a) || !assignments.contains(b)) {
        assignments
      } else {
        val assA = findParentNode(assignments, a)
        val assB = findParentNode(assignments, b)
        if (assA == assB) {
          assignments
        } else if (assA < assB) {
          assignments.updated(assB, assA)
        } else {
          assignments.updated(assA, assB)
        }
      }
    })

    // Replace all snapshot maps with the one snapshot map of the group they belong to
    def replaceSnapshotMaps(t: Term): Term = t.transform({
      case App(fun: Fun, Seq()) if
        (fun.resultSort.isInstanceOf[sorts.FieldValueFunction] || fun.resultSort.isInstanceOf[sorts.PredicateSnapFunction])
          && groups.contains(fun.id.name) =>
        App(fun.copy(id = Identifier(findParentNode(groups, fun.id.name))), Seq())
    })()
    val snapRhsUpdated = replaceSnapshotMaps(snapRhs)
    conditionalizedPcs = conditionalizedPcs.map(replaceSnapshotMaps)

    // If there is a term `Lookup(_, sm, _) == abstractLhs`, replace all occurrences of `Lookup(_, sm, _)` with `abstractLhs`
    conditionalizedPcs.find({
      case BuiltinEquals(Lookup(_, fvf, _), SortWrapper(`abstractLhs`, _)) => fvf.sort.isInstanceOf[sorts.FieldValueFunction]
      case BuiltinEquals(PredicateLookup(_, psf, _), SortWrapper(`abstractLhs`, _)) => psf.sort.isInstanceOf[sorts.PredicateSnapFunction]
      case _ => false
    }) match {
      case Some(BuiltinEquals(Lookup(_, fvf, _), _)) =>
        conditionalizedPcs = conditionalizedPcs.map(_.transform {
          case l@Lookup(_, `fvf`, _) if fvf.sort.isInstanceOf[sorts.FieldValueFunction] => SortWrapper(abstractLhs, l.sort)
        }())
      case Some(BuiltinEquals(PredicateLookup(_, psf, _), _)) =>
        conditionalizedPcs = conditionalizedPcs.map(_.transform {
          case l@PredicateLookup(_, `psf`, _) if psf.sort.isInstanceOf[sorts.PredicateSnapFunction] => SortWrapper(abstractLhs, l.sort)
        }())
      case _ =>
    }

    // Remove all path conditions of the form `p0 == p1` where p0 is syntactically equal to p1
    conditionalizedPcs = conditionalizedPcs.filter {
      case BuiltinEquals(p0, p1) => p0 != p1
      case _ => true
    }

    // Transform the term `mwsfLookup == snapRhs` into a set of equalities using First and Second constructors on `snapRhs`
    // If the resulting term is a snapshot map or a lookup of a snapshot map, substitute it with a corresponding MWSF term
    val newSnapshotMaps = freshSnapshotMaps.filter(f => {
      val id = f.func.id.name
      groups.exists({ case (from, to) => from == to && from == id })
    }).map(f => App(f.func, Seq.empty))
    def substituteMwsfTerm(snap: Term, mwsfTerm: Term, pcsList: Vector[Term]): (Vector[Term], Vector[Term]) = {
      snap match {
        case Combine(snap1, snap2) =>
          val (pcsList1, terms1) = substituteMwsfTerm(snap1, First(mwsfTerm), pcsList)
          val (pcsList2, terms2) = substituteMwsfTerm(snap2, Second(mwsfTerm), pcsList1)
          (pcsList2, terms1 ++ terms2)
        case _ =>
          var transformed = false
          val pcsListNew = snap match {
            case SortWrapper(app: App, _) if app.sort.isInstanceOf[sorts.FieldValueFunction] && newSnapshotMaps.contains(app) =>
              pcsList.map(pcs => {
                transformed = true
                pcs.transform { case Lookup(field, `app`, at) => Lookup(field, SortWrapper(mwsfTerm, app.sort), at) }()
              })
            case SortWrapper(Lookup(snapField, app: App, snapAt), _) if app.sort.isInstanceOf[sorts.FieldValueFunction] && newSnapshotMaps.contains(app) =>
              pcsList.map(pcs => {
                transformed = true
                pcs.transform { case l@Lookup(`snapField`, `app`, `snapAt`) => SortWrapper(mwsfTerm, l.sort) }()
              })
            case SortWrapper(app: App, _) if app.sort.isInstanceOf[sorts.PredicateSnapFunction] && newSnapshotMaps.contains(app) =>
              pcsList.map(pcs => {
                transformed = true
                pcs.transform { case PredicateLookup(pred, `app`, args) => PredicateLookup(pred, SortWrapper(mwsfTerm, app.sort), args) }()
              })
            case SortWrapper(PredicateLookup(snapPred, app: App, _), _) if app.sort.isInstanceOf[sorts.PredicateSnapFunction] && newSnapshotMaps.contains(app) =>
              pcsList.map(pcs => {
                transformed = true
                pcs.transform { case l@PredicateLookup(`snapPred`, `app`, _) => SortWrapper(mwsfTerm, l.sort) }()
              })
            case _ => pcsList
          }
          (pcsListNew, if (transformed) Vector.empty else Vector(BuiltinEquals(mwsfTerm, snap)))
      }
    }
    val (updatedPcs, mwsfTerms) = substituteMwsfTerm(snapRhsUpdated, mwsfApply, conditionalizedPcs)

    // Partition path conditions into a set which include the abstractLhs or any new snapshot map and those which do not
    val (pcsWithAbstractLhs, pcsWithoutAbstractLhs) = updatedPcs.partition(pcs => pcs.contains(abstractLhs))

    // Combine all path conditions which include the abstractLhs and add it to the verifier's list of definitions
    val pcsQuantified = Forall(abstractLhs, And(pcsWithAbstractLhs ++ mwsfTerms), Trigger(mwsfApply))
    v1.decider.assumeDefinition(pcsQuantified)
    pcsWithoutAbstractLhs :+ pcsQuantified
  }

  /**
   * Package a magic wand into a chunk. It performs the computation of the wand's footprint
   * and captures all values associated to these locations inside the wand's snapshot.
   *
   * {{{ package A --* B { <proofScript> } }}}
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

    def appendToRecordedBranches(s5: State,
                                 ch: Chunk,
                                 pcs: RecordedPathConditions,
                                 abstractLhs: Var,
                                 mwsf: Term,
                                 snapRhs: Term,
                                 functionsBeforePackaging: Set[FunctionDecl],
                                 v5: Verifier): VerificationResult = {
      assert(s5.conservedPcs.nonEmpty, s"Unexpected structure of s5.conservedPcs: ${s5.conservedPcs}")

      // Producing a wand's LHS and executing the packaging proof code can introduce definitional path conditions, e.g.
      // new permission and snapshot maps, which are in general necessary to proceed after the
      // package statement, e.g. to know which permissions have been consumed.
      // Here, we want to keep *only* the definitions, but no other path conditions.
      val conservedPcs: Vector[Term] = summarizeDefinitions(s5.conservedPcs.head :+ pcs.definitionsOnly, abstractLhs, mwsf, snapRhs, functionsBeforePackaging, v5)
      val conservedPcsStack: Stack[Vector[RecordedPathConditions]] =
        s5.conservedPcs.tail match {
          case empty@Seq() => empty
          case head +: tail =>
            (head ++ (s5.conservedPcs.head :+ pcs.definitionsOnly)) +: tail
        }

      val s6 = s5.copy(
        oldHeaps = s.oldHeaps,
        parallelizeBranches = s.parallelizeBranches, /* See comment below */
        reserveHeaps = s5.reserveHeaps.drop(3),
        conservedPcs = conservedPcsStack,
        recordPcs = s.recordPcs,
        exhaleExt = false,
      )

      recordedBranches :+= (s6, v5.decider.pcs.branchConditions, v5.decider.pcs.branchConditionExps, conservedPcs, ch)
      Success()
    }

    def createWandChunkAndRecordResults(s4: State,
                                        abstractLhs: Var,
                                        snapRhs: Term,
                                        functionsBeforePackaging: Set[FunctionDecl],
                                        v4: Verifier)
                                       : VerificationResult = {
      val preMark = v4.decider.setPathConditionMark()

      v.decider.prover.comment(s"Create MagicWandSnapFunction for wand $wand")
      val mwsf = v.decider.fresh("mwsf", sorts.MagicWandSnapFunction)

      // If the wand is used as a quantified resource anywhere in the program
      if (s4.qpMagicWands.contains(MagicWandIdentifier(wand, s.program))) {
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))

        evals(s4, bodyVars, _ => pve, v4)((s5, args, v5) => {
          val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s5, wand, args, SortWrapper(mwsf, sorts.Snap), v5)
          v5.decider.prover.comment("Definitional axioms for singleton-SM's value")
          v5.decider.assumeDefinition(smValueDef)
          val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, wand, args, FullPerm, sm, s.program)
          val lookupMwsf = SortWrapper(ResourceLookup(wand, sm, args, s.program), sorts.MagicWandSnapFunction)
          appendToRecordedBranches(s5, ch, v5.decider.pcs.after(preMark), abstractLhs, lookupMwsf, snapRhs, functionsBeforePackaging, v5)
        })
      } else {
        val wandSnapshot = MagicWandSnapshot(mwsf)
        this.createChunk(s4, wand, wandSnapshot, pve, v4)((s5, ch, v5) => {
          appendToRecordedBranches(s5, ch, v5.decider.pcs.after(preMark), abstractLhs, mwsf, snapRhs, functionsBeforePackaging, v5)
        })
      }
    }

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

    val tempResult = executionFlowController.locally(sEmp, v)((s1, v1) => {
      /* A snapshot (binary tree) will be constructed using First/Second datatypes,
       * that preserves the original root. The leafs of this tree will later appear
       * in the snapshot of the RHS at the appropriate places. Thus equating
       * `abstractLhs` with the snapshot received from consuming the LHS when
       * applying the wand preserves values from the LHS into the RHS.
       */
      val abstractLhs = freshSnap(sorts.Snap, v1)
      val functionsBeforePackaging = v1.decider.freshFunctions

      // Produce the wand's LHS.
      produce(s1.copy(conservingSnapshotGeneration = true), toSf(abstractLhs), wand.left, pve, v1)((sLhs, v2) => {
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
        executor.exec(s2, proofScriptCfg, v2)((sProofScript, v3) => {
          // Consume the wand's RHS and produce a snapshot which records all the values of variables on the RHS.
          // This part indirectly calls the methods `this.transfer` and `this.consumeFromMultipleHeaps`.
          val s3 = sProofScript.copy(oldHeaps = s2.oldHeaps, reserveCfgs = sProofScript.reserveCfgs.tail)
          consume(s3, wand.right, pve, v3)((s4, snapRhs, v4) =>
            createWandChunkAndRecordResults(s4, abstractLhs, snapRhs, functionsBeforePackaging, v4)
          )
        })
      })
    })

    if (recordedBranches.isEmpty) {
      // No results mean that packaging the wand resulted in inconsistent states on all paths,
      // and thus, that no wand chunk was created. In order to continue, we create one now.
      // Moreover, we need to set reserveHeaps to structurally match [State RHS] below.
      val s1 = sEmp.copy(reserveHeaps = Heap() +: Heap() +: Heap() +: s.reserveHeaps.tail)
      createWandChunkAndRecordResults(s1, freshSnap(sorts.Snap, v), freshSnap(sorts.Snap, v), v.decider.freshFunctions, v)
    }

    recordedBranches.foldLeft(tempResult)((prevRes, recordedBranch) => {
      prevRes && {
        val (s6, branchConditions, branchConditionsExp, conservedPcs, magicWandChunk) = recordedBranch

        // We execute the continuation Q in a new scope with all branch conditions and all conserved path conditions.
        executionFlowController.locally(s6, v)((s7, v7) => {
          // Set the branch conditions
          v7.decider.setCurrentBranchCondition(And(branchConditions), Some(BigAnd(branchConditionsExp.flatten)))

          // Recreate all path conditions in the Z3 proof script that we recorded for that branch
          conservedPcs.foreach(pcs => v7.decider.assume(pcs))

          // Execute the continuation Q
          Q(s7, magicWandChunk, v7)
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
        assert(snapLhs.sort == sorts.Snap, s"Expected snapshot but found: $snapLhs")

        // Create copy of the state with a new labelled heap (i.e. `oldHeaps`) called "lhs".
        val s3 = s2.copy(oldHeaps = s1.oldHeaps + (Verifier.MAGIC_WAND_LHS_STATE_LABEL -> this.getEvalHeap(s1)))

        // Convert snapWand to MWSF
        val mwsf = snapWand match {
          case SortWrapper(snapshot: MagicWandSnapshot, _) => snapshot.mwsf
          case SortWrapper(snapshot, _) => SortWrapper(snapshot, sorts.MagicWandSnapFunction)
          case _ => SortWrapper(snapWand, sorts.MagicWandSnapFunction)
        }

        // Produce the wand's RHS.
        produce(s3.copy(conservingSnapshotGeneration = true), toSf(MWSFApply(mwsf, snapLhs)), wand.right, pve, v2)((s4, v3) => {
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
