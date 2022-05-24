// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.annotation.unused
import viper.silver.cfg.silver.SilverCfg
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.verifier.{CounterexampleTransformer, PartialVerificationError}
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silver.{ast, cfg}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{CommentRecord, ConditionalEdgeRecord, ExecuteRecord, MethodCallRecord}
import viper.silicon.resources.FieldID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier

trait ExecutionRules extends SymbolicExecutionRules {
  def exec(s: State,
           cfg: SilverCfg,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult
}

object executor extends ExecutionRules {
  import consumer._
  import evaluator._
  import producer._

  private def follow(s: State, edge: SilverEdge, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
                    : VerificationResult = {

    def handleOutEdge(s: State, edge: SilverEdge, v: Verifier): State = {
      edge.kind match {
        case cfg.Kind.Out =>
          val (fr1, h1) = v.stateConsolidator.merge(s.functionRecorder, s.h, s.invariantContexts.head, v)
          val s1 = s.copy(functionRecorder = fr1, h = h1,
                          invariantContexts = s.invariantContexts.tail)
          s1
        case _ =>
          /* No need to do anything special. See also the handling of loop heads in exec below. */
          s
      }
    }

    edge match {
      case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] =>
        val condEdgeRecord = new ConditionalEdgeRecord(ce.condition, s, v.decider.pcs)
        val sepIdentifier = SymbExLogger.currentLog().openScope(condEdgeRecord)
        val s1 = handleOutEdge(s, edge, v)
        eval(s1, ce.condition, IfFailed(ce.condition), v)((s2, tCond, v1) =>
          /* Using branch(...) here ensures that the edge condition is recorded
           * as a branch condition on the pathcondition stack.
           */
          brancher.branch(s2, tCond, Some(ce.condition), v1)(
            (s3, v3) =>
              exec(s3, ce.target, ce.kind, v3)((s4, v4) => {
                SymbExLogger.currentLog().closeScope(sepIdentifier)
                Q(s4, v4)
              }),
            (_, _)  => {
              SymbExLogger.currentLog().closeScope(sepIdentifier)
              Success()
            }))

      case ue: cfg.UnconditionalEdge[ast.Stmt, ast.Exp] =>
        val s1 = handleOutEdge(s, edge, v)
        exec(s1, ue.target, ue.kind, v)(Q)
    }
  }

  private def follows(s: State,
                      edges: Seq[SilverEdge],
                      @unused pvef: ast.Exp => PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(s, v)
    } else if (edges.length == 1) {
      follow(s, edges.head, v)(Q)
    } else {
      val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(edges.length)
      val res = edges.zipWithIndex.foldLeft(Success(): VerificationResult) {
        case (result: VerificationResult, (edge, edgeIndex)) =>
          if (edgeIndex != 0) {
            SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
          }
          SymbExLogger.currentLog().markReachable(uidBranchPoint)
          result combine follow(s, edge, v)(Q)
      }
      SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
      res
    }
  }

  def exec(s: State, graph: SilverCfg, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    exec(s, graph.entry, cfg.Kind.Normal, v)(Q)
  }

  def exec(s: State, block: SilverBlock, incomingEdgeKind: cfg.Kind.Value, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    block match {
      case cfg.StatementBlock(stmt) =>
        execs(s, stmt, v)((s1, v1) =>
          follows(s1, magicWandSupporter.getOutEdges(s1, block), IfFailed, v1)(Q))

      case   _: cfg.PreconditionBlock[ast.Stmt, ast.Exp]
           | _: cfg.PostconditionBlock[ast.Stmt, ast.Exp] =>

        /* It is expected that the CFG of a method *body* is executed, not that of
         * the whole method (which includes pre-/postcondition blocks).
         * See also the MethodSupporter.
         */
        sys.error(s"Unexpected block: $block")

      case block @ cfg.LoopHeadBlock(invs, stmts, _) =>
        incomingEdgeKind match {
          case cfg.Kind.In =>
            /* We've reached a loop head block via an in-edge. Steps to perform:
             *   - Check loop invariant for self-framingness
             *   - Check that the loop guard is framed by the invariant
             *   - Exhale invariant of the target block
             *   - Push leftover state onto invariant context stack
             *   - Create state in which to execute the loop body by producing the
             *     invariant into an empty heap
             *   - Execute the statements in the loop head block
             *   - Follow the outgoing edges
             */

            /* Havoc local variables that are assigned to in the loop body */
            val wvs = s.methodCfg.writtenVars(block)
              /* TODO: BUG: Variables declared by LetWand show up in this list, but shouldn't! */

            val gBody = Store(wvs.foldLeft(s.g.values)((map, x) => map.updated(x, v.decider.fresh(x))))
            val sBody = s.copy(g = gBody, h = Heap())

            val edges = s.methodCfg.outEdges(block)
            val (outEdges, otherEdges) = edges partition(_.kind == cfg.Kind.Out)
            val sortedEdges = otherEdges ++ outEdges
            val edgeConditions = sortedEdges.collect{case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => ce.condition}
                                            .distinct

            type PhaseData = (State, RecordedPathConditions, InsertionOrderedSet[FunctionDecl])
            var phase1data: Vector[PhaseData] = Vector.empty

            (executionFlowController.locally(sBody, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Check well-definedness of invariant")
                val mark = v0.decider.setPathConditionMark()
                produces(s0, freshSnap, invs, ContractNotWellformed, v0)((s1, v1) => {
                  phase1data = phase1data :+ (s1,
                                              v1.decider.pcs.after(mark),
                                              InsertionOrderedSet.empty[FunctionDecl] /*v2.decider.freshFunctions*/ /* [BRANCH-PARALLELISATION] */)
                  v1.decider.prover.comment("Loop head block: Check well-definedness of edge conditions")
                  edgeConditions.foldLeft(Success(): VerificationResult) {
                    case (fatalResult: FatalResult, _) => fatalResult
                    case (intermediateResult, eCond) =>
                      intermediateResult && executionFlowController.locally(s1, v1)((s2, v2) => {
                        eval(s2, eCond, WhileFailed(eCond), v2)((_, _, _) =>
                          Success())})}})})
            && executionFlowController.locally(s, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Establish invariant")
                consumes(s0, invs, LoopInvariantNotEstablished, v0)((sLeftover, _, v1) => {
                  v1.decider.prover.comment("Loop head block: Execute statements of loop head block (in invariant state)")
                  phase1data.foldLeft(Success(): VerificationResult) {
                    case (fatalResult: FatalResult, _) => fatalResult
                    case (intermediateResult, (s1, pcs, _)) => /* [BRANCH-PARALLELISATION] ff1 */
                      val s2 = s1.copy(invariantContexts = sLeftover.h +: s1.invariantContexts)
                      intermediateResult && executionFlowController.locally(s2, v1)((s3, v2) => {
  //                    v2.decider.declareAndRecordAsFreshFunctions(ff1 -- v2.decider.freshFunctions) /* [BRANCH-PARALLELISATION] */
                        v2.decider.assume(pcs.assumptions)
                        v2.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
                        if (v2.decider.checkSmoke())
                          Success()
                        else {
                          execs(s3, stmts, v2)((s4, v3) => {
                            v3.decider.prover.comment("Loop head block: Follow loop-internal edges")
                            follows(s4, sortedEdges, WhileFailed, v3)(Q)})}})}})}))

          case _ =>
            /* We've reached a loop head block via an edge other than an in-edge: a normal edge or
             * and out-edge. We consider this edge to be a back-edge and we break the cycle by
             * attempting to re-establish the invariant.
             */
            v.decider.prover.comment("Loop head block: Re-establish invariant")
            consumes(s, invs, e => LoopInvariantNotPreserved(e), v)((_, _, _) =>
              Success())
        }
    }
  }

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult =

    if(stmts.nonEmpty)
      exec(s, stmts.head, v)((s1, v1) =>
        execs(s1, stmts.tail, v1)(Q))
    else
      Q(s, v)

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {
    val sepIdentifier = SymbExLogger.currentLog().openScope(new ExecuteRecord(stmt, s, v.decider.pcs))
    exec2(s, stmt, v)((s1, v1) => {
      SymbExLogger.currentLog().closeScope(sepIdentifier)
      Q(s1, v1)})
  }

  def exec2(state: State, stmt: ast.Stmt, v: Verifier)
           (continuation: (State, Verifier) => VerificationResult)
           : VerificationResult = {

    val s = state.copy(h = magicWandSupporter.getExecutionHeap(state))
    val Q: (State, Verifier) => VerificationResult = (s, v) => {
      continuation(magicWandSupporter.moveToReserveHeap(s, v), v)}

    /* For debugging-purposes only */
    stmt match {
      case _: ast.Seqn =>
      case _ =>
        v.logger.debug(s"\nEXECUTE ${viper.silicon.utils.ast.sourceLineColumn(stmt)}: $stmt")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        v.decider.prover.comment("[exec]")
        v.decider.prover.comment(stmt.toString())
    }

    val executed = stmt match {
      case ast.Seqn(stmts, _) =>
        execs(s, stmts, v)(Q)

      case ast.Label(name, _) =>
        val s1 = s.copy(oldHeaps = s.oldHeaps + (name -> magicWandSupporter.getEvalHeap(s)))
        Q(s1, v)

      case ast.LocalVarDeclStmt(decl) =>
        val x = decl.localVar
        val t = v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ))
        Q(s.copy(g = s.g + (x -> t)), v)

      case ass @ ast.LocalVarAssign(x, rhs) =>
        eval(s, rhs, AssignmentFailed(ass), v)((s1, tRhs, v1) => {
          val t = ssaifyRhs(tRhs, x.name, x.typ, v)
          Q(s1.copy(g = s1.g + (x, t)), v1)})

      /* TODO: Encode assignments e1.f := e2 as
       *         exhale acc(e1.f)
       *         inhale acc(e1.f) && e1.f == e2
       *       and benchmark possible performance effects.
       */

      /* Assignment for a field that contains quantified chunks */
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
              if s.qpFields.contains(field) =>

        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val (relevantChunks, otherChunks) =
              quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s2.h, BasicChunkIdentifier(field.name))
            val hints = quantifiedChunkSupporter.extractHints(None, Seq(tRcvr))
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s2, field, Seq(`?r`), relevantChunks, v1)
            v2.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr))
            v2.decider.clearModel()
            val result = quantifiedChunkSupporter.removePermissions(
              s2.copy(smCache = smCache1),
              relevantChunks,
              Seq(`?r`),
              `?r` === tRcvr,
              field,
              FullPerm(),
              chunkOrderHeuristics,
              v2
            )
            result match {
              case (Complete(), s3, remainingChunks) =>
                val h3 = Heap(remainingChunks ++ otherChunks)
                val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s3, field, Seq(tRcvr), tRhs, v2)
                v1.decider.prover.comment("Definitional axioms for singleton-FVF's value")
                v1.decider.assume(smValueDef)
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), field, Seq(tRcvr), FullPerm(), sm)
                v1.decider.assume(FieldTrigger(field.name, sm, tRcvr))
                Q(s3.copy(h = h3 + ch), v2)
              case (Incomplete(_), s3, _) =>
                createFailure(pve dueTo InsufficientPermission(fa), v2, s3)}}))

      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs) =>
        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val resource = fa.res(Verifier.program)
            val ve = pve dueTo InsufficientPermission(fa)
            val description = s"consume ${ass.pos}: $ass"
            chunkSupporter.consume(s2, s2.h, resource, Seq(tRcvr), FullPerm(), ve, v2, description)((s3, h3, _, v3) => {
              val tSnap = ssaifyRhs(tRhs, field.name, field.typ, v3)
              val id = BasicChunkIdentifier(field.name)
              val newChunk = BasicChunk(FieldID, id, Seq(tRcvr), tSnap, FullPerm())
              chunkSupporter.produce(s3, h3, newChunk, v3)((s4, h4, v4) =>
                Q(s4.copy(h = h4), v4))
            })
          })
        )

      case ast.NewStmt(x, fields) =>
        val tRcvr = v.decider.fresh(x)
        v.decider.assume(tRcvr !== Null())
        val newChunks = fields map (field => {
          val p = FullPerm()
          val snap = v.decider.fresh(field.name, v.symbolConverter.toSort(field.typ))
          if (s.qpFields.contains(field)) {
            val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, field, Seq(tRcvr), snap, v)
            v.decider.prover.comment("Definitional axioms for singleton-FVF's value")
            v.decider.assume(smValueDef)
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), field, Seq(tRcvr), p, sm)
          } else {
            BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), snap, p)
          }
        })
        val ts = viper.silicon.state.utils.computeReferenceDisjointnesses(s, tRcvr)
        val s1 = s.copy(g = s.g + (x, tRcvr), h = s.h + Heap(newChunks))
        v.decider.assume(ts)
        Q(s1, v)

      case inhale @ ast.Inhale(a) => a match {
        case _: ast.FalseLit =>
          /* We're done */
          Success()
        case _ =>
          produce(s, freshSnap, a, InhaleFailed(inhale), v)((s1, v1) => {
            v1.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterInhale)
            Q(s1, v1)})
      }

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(s, a, pve, v)((s1, _, v1) =>
          Q(s1, v1))

      case assert @ ast.Assert(a: ast.FalseLit) =>
        /* "assert false" triggers a smoke check. If successful, we backtrack. */
        executionFlowController.tryOrFail0(s.copy(h = magicWandSupporter.getEvalHeap(s)), v)((s1, v1, QS) => {
          if (v1.decider.checkSmoke())
            QS(s1.copy(h = s.h), v1)
          else
            createFailure(AssertFailed(assert) dueTo AssertionFalse(a), v1, s1, true)
        })((_, _) => Success())

      case assert @ ast.Assert(a) if Verifier.config.disableSubsumption() =>
        val r =
          consume(s, a, AssertFailed(assert), v)((_, _, _) =>
            Success())

        r combine Q(s, v)

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        if (s.exhaleExt) {
          Predef.assert(s.h.values.isEmpty)
          Predef.assert(s.reserveHeaps.head.values.isEmpty)

          /* When exhaleExt is set magicWandSupporter.transfer is used to transfer permissions to
           * hUsed (reserveHeaps.head) instead of consuming them. hUsed is later discarded and replaced
           * by s.h. By copying hUsed to s.h the contained permissions remain available inside the wand.
           */
          consume(s, a, pve, v)((s2, _, v1) => {
            Q(s2.copy(h = s2.reserveHeaps.head), v1)
          })
        } else
          consume(s, a, pve, v)((s1, _, v1) => {
            val s2 = s1.copy(h = s.h, reserveHeaps = s.reserveHeaps)
            Q(s2, v1)})

      // Calling hack407_R() results in Silicon efficiently havocking all instances of resource R.
      // See also Silicon issue #407.
      case ast.MethodCall(methodName, _, _)
          if !Verifier.config.disableHavocHack407() && methodName.startsWith(hack407_method_name_prefix) =>

        val resourceName = methodName.stripPrefix(hack407_method_name_prefix)
        val member = Verifier.program.collectFirst {
          case m: ast.Field if m.name == resourceName => m
          case m: ast.Predicate if m.name == resourceName => m
        }.getOrElse(sys.error(s"Found $methodName, but no matching field or predicate $resourceName"))
        val h1 = Heap(s.h.values.map {
          case bc: BasicChunk if bc.id.name == member.name =>
            bc.withSnap(freshSnap(bc.snap.sort, v))
          case qfc: QuantifiedFieldChunk if qfc.id.name == member.name =>
            qfc.withSnapshotMap(freshSnap(qfc.fvf.sort, v))
          case qpc: QuantifiedPredicateChunk if qpc.id.name == member.name =>
            qpc.withSnapshotMap(freshSnap(qpc.psf.sort, v))
          case other =>
            other})
        Q(s.copy(h = h1), v)

      // Calling hack510() triggers a state consolidation.
      // See also Silicon issue #510.
      case ast.MethodCall(`hack510_method_name`, _, _) =>
        val s1 = v.stateConsolidator.consolidate(s, v)
        Q(s1, v)

      case call @ ast.MethodCall(methodName, eArgs, lhs) =>
        val meth = Verifier.program.findMethod(methodName)
        val fargs = meth.formalArgs.map(_.localVar)
        val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs).to(Map)
        val reasonTransformer = (n: viper.silver.verifier.errors.ErrorNode) => n.replace(formalsToActuals)
        val pveCall = CallFailed(call).withReasonNodeTransformed(reasonTransformer)

        val mcLog = new MethodCallRecord(call, s, v.decider.pcs)
        val currentLog = SymbExLogger.currentLog()
        val sepIdentifier = currentLog.openScope(mcLog)
        val paramLog = new CommentRecord("Parameters", s, v.decider.pcs)
        val paramId = currentLog.openScope(paramLog)
        evals(s, eArgs, _ => pveCall, v)((s1, tArgs, v1) => {
          currentLog.closeScope(paramId)
          val exampleTrafo = CounterexampleTransformer({
            case ce: SiliconCounterexample => ce.withStore(s1.g)
            case ce => ce
          })
          val pvePre = ErrorWrapperWithExampleTransformer(PreconditionInCallFalse(call).withReasonNodeTransformed(reasonTransformer), exampleTrafo)
          val preCondLog = new CommentRecord("Precondition", s1, v1.decider.pcs)
          val preCondId = currentLog.openScope(preCondLog)
          val s2 = s1.copy(g = Store(fargs.zip(tArgs)),
                           recordVisited = true)
          consumes(s2, meth.pres, _ => pvePre, v1)((s3, _, v2) => {
            currentLog.closeScope(preCondId)
            val postCondLog = new CommentRecord("Postcondition", s3, v2.decider.pcs)
            val postCondId = currentLog.openScope(postCondLog)
            val outs = meth.formalReturns.map(_.localVar)
            val gOuts = Store(outs.map(x => (x, v2.decider.fresh(x))).toMap)
            val s4 = s3.copy(g = s3.g + gOuts, oldHeaps = s3.oldHeaps + (Verifier.PRE_STATE_LABEL -> s1.h))
            produces(s4, freshSnap, meth.posts, _ => pveCall, v2)((s5, v3) => {
              currentLog.closeScope(postCondId)
              v3.decider.prover.saturate(Verifier.config.proverSaturationTimeouts.afterContract)
              val gLhs = Store(lhs.zip(outs)
                              .map(p => (p._1, s5.g(p._2))).toMap)
              val s6 = s5.copy(g = s1.g + gLhs,
                               oldHeaps = s1.oldHeaps,
                               recordVisited = s1.recordVisited)
              currentLog.closeScope(sepIdentifier)
              Q(s6, v3)})})})

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, ePerm, pve, v2)((s3, v3) => {
              val wildcards = s3.constrainableARPs -- s1.constrainableARPs
              predicateSupporter.fold(s3, predicate, tArgs, tPerm, wildcards, pve, v3)(Q)})))

      case unfold @ ast.Unfold(ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {

            val smCache1 = if (s2.qpPredicates.contains(predicate)) {
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s2.h, BasicChunkIdentifier(predicateName))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v2)
              v2.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs))
              smCache1
            } else {
              s2.smCache
            }

            permissionSupporter.assertNotNegative(s2, tPerm, ePerm, pve, v2)((s3, v3) => {
              val wildcards = s3.constrainableARPs -- s1.constrainableARPs
              predicateSupporter.unfold(s3.copy(smCache = smCache1), predicate, tArgs, tPerm, wildcards, pve, v3, pa)(Q)
            })
          }))

      case pckg @ ast.Package(wand, proofScript) =>
        val pve = PackageFailed(pckg)
          magicWandSupporter.packageWand(s, wand, proofScript, pve, v)((s1, chWand, v1) => {

            val hOps = s1.reserveHeaps.head + chWand
            assert(s.exhaleExt || s1.reserveHeaps.length == 1)
            val s2 =
              if (s.exhaleExt) {
                s1.copy(h = Heap(),
                        exhaleExt = true,
                        /* It is assumed, that s.reserveHeaps.head (hUsed) is not used or changed
                         * by the packageWand method. hUsed is normally used during transferring
                         * consume to store permissions that have already been consumed. The
                         * permissions on this heap should be discarded after a statement finishes
                         * execution. hUsed should therefore be empty unless the package statement
                         * was triggered by heuristics during a consume operation.
                         */
                        reserveHeaps = s.reserveHeaps.head +: hOps +: s1.reserveHeaps.tail)
              } else {
                /* c1.reserveHeap is expected to be [σ.h'], i.e. the remainder of σ.h */
                s1.copy(h = hOps,
                        exhaleExt = false,
                        reserveHeaps = Nil)
              }
            assert(s2.reserveHeaps.length == s.reserveHeaps.length)

            val smCache3 = chWand match {
              case ch: QuantifiedMagicWandChunk =>
                val (relevantChunks, _) =
                  quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s2.h, ch.id)
                val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
                val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ)))
                val (smDef, smCache) =
                  quantifiedChunkSupporter.summarisingSnapshotMap(
                    s2, wand, formalVars, relevantChunks, v1)
                v1.decider.assume(PredicateTrigger(ch.id.toString, smDef.sm, ch.singletonArgs.get))
                smCache
              case _ => s2.smCache
            }

            continuation(s2.copy(smCache = smCache3), v1)
          })

      case apply @ ast.Apply(e) =>
        val pve = ApplyFailed(apply)
        magicWandSupporter.applyWand(s, e, pve, v)(Q)

      case viper.silicon.extensions.TryBlock(body) =>
        var bodySucceeded = false
        val bodyResult = exec(s, body, v)((s1, v2) => {
          bodySucceeded = true
          Q(s1, v2)
        })
        if (bodySucceeded) bodyResult
        else Q(s, v)

      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: ast.Goto
           | _: ast.If
           | _: ast.Label
           | _: ast.Seqn
           | _: ast.Assume
           | _: ast.ExtensionStmt
           | _: ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")
    }

    executed
  }

   private def ssaifyRhs(rhs: Term, name: String, typ: ast.Type, v: Verifier): Term = {
     rhs match {
       case _: Var | _: Literal =>
         rhs

       case _  =>
         /* 2018-06-05 Malte:
          *   This case was previously guarded by the condition
          *     rhs.existsDefined {
          *       case t if v.triggerGenerator.isForbiddenInTrigger(t) => true
          *     }
          *   and followed by a catch-all case in which rhs was returned.
          *   However, reducing the number of fresh symbols does not appear to improve
          *   performance; instead, it can cause an exponential blow-up in term size, as
          *   reported by Silicon issue #328.
          */
         val t = v.decider.fresh(name, v.symbolConverter.toSort(typ))
         v.decider.assume(t === rhs)

         t
     }
   }

  private val hack407_method_name_prefix = "___silicon_hack407_havoc_all_"

  def hack407_havoc_all_resources_method_name(id: String): String = s"$hack407_method_name_prefix$id"

  def hack407_havoc_all_resources_method_call(id: String): ast.MethodCall = {
    ast.MethodCall(
      methodName = hack407_havoc_all_resources_method_name(id),
      args = Vector.empty,
      targets = Vector.empty
    )(ast.NoPosition, ast.NoInfo, ast.NoTrafos)
  }

  private val hack510_method_name = "___silicon_hack510_consolidate_state"
}
