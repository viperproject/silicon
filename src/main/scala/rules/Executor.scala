/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.Stack
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsNonNegative
import viper.silicon.state.{FieldChunk, Heap, State, Store}
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier
import viper.silver.cfg.silver.SilverCfg
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silver.{ast, cfg}

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

object executor extends ExecutionRules with Immutable {
  import consumer._
  import evaluator._
  import producer._

  private def follow(s: State, edge: SilverEdge, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
                    : VerificationResult = {

    val s1 = edge.kind match {
      case cfg.Kind.Out =>
        val s1 = s.copy(h = stateConsolidator.merge(s.h, s.invariantContexts.head, v),
                        invariantContexts = s.invariantContexts.tail)
        s1
      case _ =>
        /* No need to do anything special. See also the handling of loop heads in exec below. */
        s
    }

    edge match {
      case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] =>
        eval(s1, ce.condition, IfFailed(ce.condition), v)((s2, tCond, v1) =>
          /* Using branch(...) here ensures that the edge condition is recorded
           * as a branch condition on the pathcondition stack.
           */
          brancher.branch(s2, tCond, v1,
            (s3, v3) => exec(s3, ce.target, ce.kind, v3)(Q),
            (_, _)  => Success()))

      case ue: cfg.UnconditionalEdge[ast.Stmt, ast.Exp] =>
        exec(s1, ue.target, ue.kind, v)(Q)
    }
  }

  private def follows(s: State,
                      edges: Seq[SilverEdge],
                      pvef: ast.Exp => PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(s, v)
    } else
      edges.foldLeft(Success(): VerificationResult) {
        case (fatalResult: FatalResult, _) => fatalResult
        case (_, edge) => follow(s, edge, v)(Q)
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

      case block @ cfg.LoopHeadBlock(invs, stmts) =>
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
                    case (intermediateResult, (s1, pcs, ff1)) =>
                      val s2 = s1.copy(invariantContexts = sLeftover.h +: s1.invariantContexts)
                      intermediateResult && executionFlowController.locally(s2, v1)((s3, v2) => {
//                    v2.decider.declareAndRecordAsFreshFunctions(ff1 -- v2.decider.freshFunctions) /* [BRANCH-PARALLELISATION] */
                      v2.decider.assume(pcs.assumptions)
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

      case cfg.ConstrainingBlock(vars: Seq[ast.AbstractLocalVar @unchecked], body: SilverCfg) =>
        val arps = vars map s.g.apply
        exec(s.setConstrainable(arps, true), body, v)((s1, v1) =>
          follows(s1.setConstrainable(arps, false), magicWandSupporter.getOutEdges(s1, block), Internal(_), v1)(Q))
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
//    val sepIdentifier = SymbExLogger.currentLog().insert(new ExecuteRecord(stmt, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    exec2(s, stmt, v)((s1, v1) => {
//      SymbExLogger.currentLog().collapse(stmt, sepIdentifier)
      Q(s1, v1)})
  }

  def exec2(state: State, stmt: ast.Stmt, v: Verifier)
          (continuation: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    val s = state.copy(h=magicWandSupporter.getExecutionHeap(state))
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
      case ast.Seqn(stmts) =>
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

      /* Assignment for a field that contains quantified chunks */
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
              if s.qpFields.contains(field) =>

        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val hints = quantifiedChunkSupporter.extractHints(None, None, tRcvr)
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            quantifiedChunkSupporter.splitSingleLocation(s2, s2.h, field, tRcvr, FullPerm(), chunkOrderHeuristics, v2) {
              case Some((s3, h3, _, _)) =>
                val (fvf, optFvfDef) = quantifiedChunkSupporter.createSingletonFieldValueFunction(s2, field, tRcvr, tRhs, v2)
                optFvfDef.foreach(fvfDef => v2.decider.assume(fvfDef.domainDefinitions ++ fvfDef.valueDefinitions))
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(tRcvr, field.name, fvf, FullPerm())
                Q(s3.copy(h = h3 + ch), v2)
              case None =>
                Failure(pve dueTo InsufficientPermission(fa))}}))

      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs) =>
        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) =>
            chunkSupporter.withChunk(s2, field.name, Seq(tRcvr), Some(FullPerm()), fa, pve, v2)((s3, fc, v3) => {
              val t = ssaifyRhs(tRhs, field.name, field.typ, v3)
              Q(magicWandSupporter.replaceChunk(s3, fc, FieldChunk(tRcvr, field.name, t, fc.perm)), v3)})))

      case ast.NewStmt(x, fields) =>
        val tRcvr = v.decider.fresh(x)
        v.decider.assume(tRcvr !== Null())
        /* TODO: Verify similar to the code in DefaultProducer/ast.FieldAccessPredicate - unify */
        val newChunks = fields map (field => {
          val p = FullPerm()
          val snap = v.decider.fresh(field.name, v.symbolConverter.toSort(field.typ))
          if (s.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createSingletonFieldValueFunction(s, field, tRcvr, snap, v)
            optFvfDef.foreach(fvfDef => v.decider.assume(fvfDef.domainDefinitions ++ fvfDef.valueDefinitions))
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(tRcvr, field.name, fvf, p)
          } else
            FieldChunk(tRcvr, field.name, snap, p)})
        val s1 = s.copy(g = s.g + (x, tRcvr), h = s.h + Heap(newChunks))
        val ts = viper.silicon.state.utils.computeReferenceDisjointnesses(s1, tRcvr)
          /* Calling computeReferenceDisjointnesses with the updated state σ1 ensures that
           * tRcvr is constrained to be different from (ref-typed) fields of tRcvr to which
           * permissions have been gained.
           * Note that we do not constrain the (ref-typed) fields to be mutually disjoint.
           */
        v.decider.assume(ts)
        Q(s1, v)

      case ast.Fresh(vars) =>
        val (arps, arpConstraints) =
          vars.map(x => (x, v.decider.freshARP()))
              .map{case (variable, (value, constrain)) => ((variable, value), constrain)}
              .unzip
        val g1 = Store(s.g.values ++ arps)
          /* It is crucial that the (var -> term) mappings in arps override
           * already existing bindings for the same vars when they are added
           * (via ++).
           */
        v.decider.assume(arpConstraints)
        Q(s.copy(g = g1), v)

      case inhale @ ast.Inhale(a) => a match {
        case _: ast.FalseLit =>
          /* We're done */
          Success()
        case _ =>
          produce(s, freshSnap, a, InhaleFailed(inhale), v)(Q)
      }

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(s, a, pve, v)((s1, _, v1) =>
          Q(s1, v1))

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.TrueLit =>
            val s1 = stateConsolidator.consolidate(s, v)
            Q(s1, v)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.FalseLit =>
            executionFlowController.tryOrFail0(s, v)((s1, v1, QS) => {
              if (v1.decider.checkSmoke())
                QS(s1, v1)
              else
                Failure(pve dueTo AssertionFalse(a))
              })((_, _) => Success())

          case _ =>
            if (Verifier.config.disableSubsumption()) {
              val r =
                consume(s, a, pve, v)((_, _, _) =>
                  Success())
              r && Q(s, v)
            } else
              consume(s.copy(recordEffects = false), a, pve, v)((s1, _, v1) => {
                val s2 = s1.copy(h = s.h, reserveHeaps = s.reserveHeaps, recordEffects = s.recordEffects)
                Q(s2, v1)})
        }

      case call @ ast.MethodCall(methodName, eArgs, lhs) =>
        val meth = Verifier.program.findMethod(methodName)
        val pvefCall = (_: ast.Exp) =>  CallFailed(call)
        val pvefPre = (_: ast.Exp) =>  PreconditionInCallFalse(call)
//        val mcLog = new MethodCallRecord(call, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]])
//        val sepIdentifier = SymbExLogger.currentLog().insert(mcLog)
        evals(s, eArgs, pvefCall, v)((s1, tArgs, v1) => {
//          mcLog.finish_parameters()
          val s2 = s1.copy(g = Store(meth.formalArgs.map(_.localVar).zip(tArgs)),
                           recordVisited = true)
          consumes(s2, meth.pres, pvefPre, v1)((s3, _, v2) => {
//            mcLog.finish_precondition()
            val outs = meth.formalReturns.map(_.localVar)
            val gOuts = Store(outs.map(x => (x, v2.decider.fresh(x))).toMap)
            val s4 = s3.copy(g = s3.g + gOuts, oldHeaps = s3.oldHeaps + (Verifier.PRE_STATE_LABEL -> s1.h))
            produces(s4, freshSnap, meth.posts, pvefCall, v2)((s5, v3) => {
//              mcLog.finish_postcondition()
              val gLhs = Store(lhs.zip(outs)
                              .map(p => (p._1, s5.g(p._2))).toMap)
              val s6 = s5.copy(g = s1.g + gLhs,
                               oldHeaps = s1.oldHeaps,
                               recordVisited = s1.recordVisited)
//              SymbExLogger.currentLog().collapse(null, sepIdentifier)
              Q(s6, v3)})})})

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
            eval(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
              v2.decider.assert(IsNonNegative(tPerm)){
                case true =>
                  //handles both quantified and unquantified predicates
                  predicateSupporter.fold(s2, predicate, tArgs, tPerm, pve, v2)(Q)
                case false =>
                  Failure(pve dueTo NegativePermission(ePerm))}))
      case unfold @ ast.Unfold(ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
            v2.decider.assert(IsNonNegative(tPerm)){
              case true =>
                //handles both quantified and unquantified predicates
                predicateSupporter.unfold(s2, predicate, tArgs, tPerm, pve, v2, pa)(Q)
              case false =>
                Failure(pve dueTo NegativePermission(ePerm))}))

      case pckg @ ast.Package(wand, proofScript) => {
        val pve = PackageFailed(pckg)
        if (s.exhaleExt) {
          magicWandSupporter.packageWand(s, wand, proofScript, pve, v)((s1, chWand, v1) => {
            val hOps = s1.reserveHeaps.head + chWand
            val s2 = s1.copy(exhaleExt = true,
              reserveHeaps = Heap() +: hOps +: s1.reserveHeaps.tail,
              lhsHeap = None)
            assert(s2.reserveHeaps.length == s.reserveHeaps.length)
            assert(s2.consumedChunks.length == s.consumedChunks.length)
            assert(s2.consumedChunks.length == s2.reserveHeaps.length - 1)
            val sEmp = s2.copy(h = Heap())
            continuation(sEmp, v1)
          })
        } else {
          val s1 = s.copy(reserveHeaps = Heap() :: s.h :: Nil,
            recordEffects = true,
            consumedChunks = Nil :: Nil,
            letBoundVars = Nil)
          magicWandSupporter.packageWand(s1, wand, proofScript, pve, v)((s2, chWand, v1) => {
            assert(s2.reserveHeaps.length == 1)
            /* c1.reserveHeap is expected to be [σ.h'], i.e. the remainder of σ.h */
            val s3 = s2.copy(h = s2.reserveHeaps.head + chWand,
              exhaleExt = false,
              reserveHeaps = Nil,
              lhsHeap = None,
              recordEffects = false,
              consumedChunks = Stack(),
              letBoundVars = Nil)
            Q(s3, v1)
          })
        }}

      case apply @ ast.Apply(e) => {
        /* TODO: Try to unify this code with that from DefaultConsumer/applying */

        val pve = ApplyFailed(apply)

        def QL(s1: State, g: Store, wand: ast.MagicWand, v1: Verifier) = {
          /* The lhs-heap is not s1.h, but rather the consumed portion only. However,
           * using s1.h should not be a problem as long as the heap that is used as
           * the given-heap while checking self-framingness of the wand is the heap
           * described by the left-hand side.
           */
          val consumeState = s1.copy(g = g)
          consume(consumeState, wand.left, pve, v1)((s2, _, v2) => {
            val s3 = magicWandSupporter.moveToReserveHeap(s2, v2).copy(lhsHeap = Some(magicWandSupporter.getEvalHeap(s1)))
            produce(s3, freshSnap, wand.right, pve, v2)((s4, v3) => {
              val s5 = s4.copy(g = s1.g,
                               lhsHeap = s1.lhsHeap)
              val s6 = stateConsolidator.consolidate(s5, v3)
              Q(s6, v3)})})}

        e match {
          case wand: ast.MagicWand => {
            consume(s, wand, pve, v)((s1, _, v1) => {
              QL(s1, s1.g, wand, v1)
            })
          }

          case _ => sys.error(s"Expected a magic wand, but found node $e")}}


      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: ast.Goto
           | _: ast.If
           | _: ast.Label
           | _: ast.Seqn
           | _: ast.Constraining
           | _: ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")
    }

    executed
  }

   private def ssaifyRhs(rhs: Term, name: String, typ: ast.Type, v: Verifier): Term =
     rhs match {
       case _: Var | _: Literal =>
         /* Cheap (and likely to succeed) matches come first */
         rhs

       case _ if    rhs.existsDefined { case t if v.triggerGenerator.isForbiddenInTrigger(t) => true }
                 || rhs.isInstanceOf[WildcardPerm] /* Fixes issue #110 (somewhat indirectly) */
            =>

         val t = v.decider.fresh(name, v.symbolConverter.toSort(typ))
         v.decider.assume(t === rhs)

         t

       case _ =>
         /* Catch-all case */
         rhs
     }
}
