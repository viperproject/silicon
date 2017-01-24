/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silicon.Stack
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.state.{FieldChunk, Heap, State, Store}
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsNonNegative
import viper.silicon.utils.freshSnap
import viper.silicon.verifier.Verifier

trait ExecutionRules extends SymbolicExecutionRules {
  def exec(s: State,
           block: ast.Block,
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

  private def follow(s: State, edge: ast.Edge, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
                    : VerificationResult = {

    edge match {
      case ue: ast.UnconditionalEdge => exec(s, ue.dest, v)(Q)
      case ce: ast.ConditionalEdge => sys.error(s"Unexpected conditional edge: $ce")
    }
  }

  private def follows(s: State, edges: Seq[ast.Edge], v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(s, v)
    } else
      follows2(s, edges, v)(Q)
  }

  private def follows2(s: State, edges: Seq[ast.Edge], v: Verifier)
                      (Q: (State, Verifier) => VerificationResult)
                      : VerificationResult = {

    if (edges.isEmpty) {
      Success()
    } else {
      follow(s, edges.head, v)(Q) && follows2(s, edges.tail, v)(Q)
    }
  }

  private def leave(s: State, block: ast.Block, v: Verifier)
                   (Q: (State, Verifier) => VerificationResult)
                   : VerificationResult = {

    follows(s, block.succs, v)(Q)
  }

  def exec(s: State, block: ast.Block, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    block match {
      case cblock @ ast.ConditionalBlock(stmt, _, _, _) =>
        exec(s, stmt, v)((s1, v1) => {
          val thn_edge = cblock.succs.head
          val els_edge = cblock.succs(1)

          assert(els_edge.cond == ast.Not(thn_edge.cond)(),
                   s"Unexpected mismatch: else-branch condition ${els_edge.cond} is not "
                 + s"syntactically the negation of the then-branch condition ${thn_edge.cond}")

          eval(s1, thn_edge.cond, IfFailed(thn_edge.cond), v1)((s2, tCond, v2) => {
            brancher.branch(s2, tCond, v2,
              (s3, v3) => exec(s3, thn_edge.dest, v3)(Q),
              (s3, v3) => exec(s3, els_edge.dest, v3)(Q))})})

      case block @ ast.StatementBlock(stmt, _) =>
        exec(s, stmt, v)((s1, v1) =>
          leave(s1, block, v1)(Q))

      case lb: ast.LoopBlock =>
        v.decider.prover.comment(s"loop at ${lb.pos}")

        /* TODO: We should avoid roundtripping, i.e., parsing a SIL file into an AST,
         *       which is then converted into a CFG, from which we then compute an
         *       AST again.
         */
        val loopStmt = lb.toAst.asInstanceOf[ast.While]
        val notGuard = ast.Not(lb.cond)(lb.cond.pos, lb.cond.info)

        /* Havoc local variables that are assigned to in the loop body but
         * that have been declared outside of it, i.e. before the loop.
         */
        val wvs = (lb.locals.map(_.localVar) ++ lb.writtenVars).distinct.filterNot(_.typ == ast.Wand)
          /* TODO: BUG: Variables declared by LetWand show up in this list, but shouldn't! */

        val gBody = Store(wvs.foldLeft(s.g.values)((map, x) => map.updated(x, v.decider.fresh(x))))
        val sBody = s.copy(g = gBody, h = Heap())

        type PhaseData = (State, RecordedPathConditions, InsertionOrderedSet[FunctionDecl])
        var phase1data: Vector[PhaseData] = Vector.empty
        var phase2data: Vector[PhaseData] = Vector.empty

        (  executionFlowController.locally(sBody/*.copy(parallelizeBranches = false)*/, v)((s0, v0) => {
              val mark = v0.decider.setPathConditionMark()
//              println("==== Loop: Check specs well-definedness ==== ")
              v0.decider.prover.comment("Loop: Check specs well-definedness")
              produces(s0, freshSnap, lb.invs, ContractNotWellformed, v0)((s1, v1) =>
                produce(s1, freshSnap, lb.cond, WhileFailed(loopStmt), v1)((s2, v2) => {
                  /* Detect potential contradictions between path conditions from the loop guard and
                   * from the invariant (e.g. due to conditionals)
                   */
                  if (!v2.decider.checkSmoke()) {
//                    println(s"  ${Thread.currentThread().getId} | ${v2.uniqueId}")
                    phase1data = phase1data :+ (s2, v2.decider.pcs.after(mark), v2.decider.freshFunctions)
                  }
                  Success()}))})
        && executionFlowController.locally(s/*.copy(parallelizeBranches = false)*/, v)((s0, v0) => {
              val mark = v0.decider.setPathConditionMark()
//              println("==== Loop: Establish loop invariant ==== ")
//              println("\n[exec/while AAAAAA]")
//              println(s"  mark = $mark")
//              println(s"  v0.uniqueId = ${v0.uniqueId}")
//              println(s"  v0.decider.pcs = ${v0.decider.pcs}")
              v0.decider.prover.comment("Loop: Establish loop invariant")
              consumes(s0, lb.invs, e => LoopInvariantNotEstablished(e), v0)((s1, _, v1) => {
//              println("\n[exec/while BBBBBBBB]")
//              println(s"  v1.uniqueId = ${v1.uniqueId}")
//              println(s"  v1.decider.pcs = ${v1.decider.pcs}")
//                println(s"  ${Thread.currentThread().getId} | ${v1.uniqueId}")
                phase2data = phase2data :+ (s1, v1.decider.pcs.after(mark), v1.decider.freshFunctions)
                Success()})})
        && {
//              println("==== Loop: Verify loop body ==== ")
              v.decider.prover.comment("Loop: Verify loop body")
              phase1data.foldLeft(Success(): VerificationResult) {
                case (fatalResult: FatalResult, _) => fatalResult
                case (intermediateResult, (s0, pcs1, ff1)) =>
                  intermediateResult && executionFlowController.locally(s0/*.copy(parallelizeBranches = s.parallelizeBranches)*/, v)((s1, v1) => {
                    v1.decider.declareAndRecordAsFreshFunctions(ff1 -- v1.decider.freshFunctions)
                    v1.decider.assume(pcs1.assumptions)
                    exec(s1, lb.body, v1)((s2, v2) =>
                      consumes(s2, lb.invs, e => LoopInvariantNotPreserved(e), v2)((_, _, _) => {
//                        println(s"  ${Thread.currentThread().getId} | ${v.uniqueId} | ${v3.uniqueId}")
                        Success()}))})}}
        && {
//              println("==== Loop: Continue after loop ==== ")
              v.decider.prover.comment("Loop: Continue after loop")
              phase2data.foldLeft(Success(): VerificationResult) {
                case (fatalResult: FatalResult, _) => fatalResult
                case (intermediateResult, (s0, pcs1, ff1)) =>
//                  println(s"  ${Thread.currentThread().getId} | ${v.uniqueId} | ${v0.uniqueId}")
                  intermediateResult && executionFlowController.locally(s0/*.copy(parallelizeBranches = s.parallelizeBranches)*/, v)((s1, v1) => {
//                    v1.decider.prover.comment(s"v0.uniqueId = ${v0.uniqueId}")
//                    v1.decider.prover.comment(s"v.uniqueId = ${v.uniqueId}")
                    v1.decider.declareAndRecordAsFreshFunctions(ff1 -- v1.decider.freshFunctions)
                    v1.decider.assume(pcs1.assumptions)
                    produces(s1.copy(g = gBody), freshSnap,  lb.invs :+ notGuard, _ => WhileFailed(loopStmt), v1)((s2, v2) =>
                      /* Detect potential contradictions (as before) */
                      if (v2.decider.checkSmoke())
                        Success() /* TODO: Mark branch as dead? */
                      else
                        leave(s2, lb, v2)(Q))})}})

        case frp @ ast.ConstrainingBlock(vars, body, _) =>
          val arps = vars map s.g.apply
          val s1 = s.setConstrainable(arps, true)
          exec(s1, body, v)((s2, v1) =>
            leave(s2.setConstrainable(arps, false), frp, v1)(Q))
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

  def exec2(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    /* For debugging-purposes only */
    stmt match {
      case _: ast.Seqn =>
      case _ =>
        v.logger.debug(s"\nEXECUTE ${viper.silicon.utils.ast.sourceLineColumn(stmt)}: $stmt")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        v.decider.prover.comment("[exec]")
        v.decider.prover.comment(stmt.toString())
    }

    val executed = stmt match {
      case ast.Seqn(stmts) =>
        execs(s, stmts, v)(Q)

      case ast.Label(name, _) =>
        val s1 = s.copy(oldHeaps = s.oldHeaps + (name -> s.h))
        Q(s1, v)

      case ass @ ast.LocalVarAssign(x, rhs) =>
        x.typ match {
          case ast.Wand =>
            assert(rhs.isInstanceOf[ast.MagicWand], s"Expected magic wand but found $rhs (${rhs.getClass.getName}})")
            val wand = rhs.asInstanceOf[ast.MagicWand]
            val pve = LetWandFailed(ass)
            magicWandSupporter.createChunk(s, wand, pve, v)((s1, chWand, v1) =>
              Q(s1.copy(g = s1.g + (x, MagicWandChunkTerm(chWand))), v1))
          case _ =>
            eval(s, rhs, AssignmentFailed(ass), v)((s1, tRhs, v1) => {
              val t = ssaifyRhs(tRhs, x.name, x.typ, v)
              Q(s1.copy(g = s1.g + (x, t)), v1)})
        }

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
                val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, tRcvr, tRhs, v2)
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
              Q(s3.copy(h = s3.h - fc + FieldChunk(tRcvr, field.name, t, fc.perm)), v3)})))

      case ast.NewStmt(x, fields) =>
        val tRcvr = v.decider.fresh(x)
        v.decider.assume(tRcvr !== Null())
        /* TODO: Verify similar to the code in DefaultProducer/ast.FieldAccessPredicate - unify */
        val newChunks = fields map (field => {
          val p = FullPerm()
          val snap = v.decider.fresh(field.name, v.symbolConverter.toSort(field.typ))
          if (s.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, tRcvr, snap, v)
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
            executionFlowController.tryOrFail(s, v)((s1, v1, QS, QF) => {
              if (v1.decider.checkSmoke())
                QS(s1, v1)
              else
                QF(Failure(pve dueTo AssertionFalse(a)))
              })((_, _) => Success())

          case ast.LocalVar("SLEEP") => /* TODO: Remove once parallelisation is implemented */
            Thread.sleep(2000)
            Q(s, v)

          case _ =>
            if (Verifier.config.disableSubsumption()) {
              val r =
                consume(s, a, pve, v)((_, _, _) =>
                  Success())
              r && Q(s, v)
            } else
              consume(s, a, pve, v)((s1, _, v1) => {
                val s2 = s1.copy(h = s.h)
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

      case pckg @ ast.Package(wand) =>
        val pve = PackageFailed(pckg)
        val s1 = s.copy(reserveHeaps = Heap() :: s.h :: Nil,
                        recordEffects = true,
                        consumedChunks = Nil :: Nil,
                        letBoundVars = Nil)
        magicWandSupporter.packageWand(s1, wand, pve, v)((s2, chWand, v1) => {
          assert(s2.reserveHeaps.length == 1) /* c1.reserveHeap is expected to be [σ.h'], i.e. the remainder of σ.h */
          val s3 = s2.copy(h = s2.reserveHeaps.head + chWand,
                           exhaleExt = false,
                           reserveHeaps = Nil,
                           lhsHeap = None,
                           recordEffects = false,
                           consumedChunks = Stack(),
                           letBoundVars = Nil)
          Q(s3, v1)})

      case apply @ ast.Apply(e) =>
        /* TODO: Try to unify this code with that from DefaultConsumer/applying */

        val pve = ApplyFailed(apply)

        def QL(s1: State, g: Store, wand: ast.MagicWand, v1: Verifier) = {
          /* The lhs-heap is not s1.h, but rather the consumed portion only. However,
           * using s1.h should not be a problem as long as the heap that is used as
           * the given-heap while checking self-framingness of the wand is the heap
           * described by the left-hand side.
           */
          consume(s1.copy(g = g), wand.left, pve, v1)((s2, _, v2) => {
            val s3 = s2.copy(lhsHeap = Some(s1.h))
            produce(s3, freshSnap, wand.right, pve, v2)((s4, v3) => {
              val s5 = s4.copy(g = s1.g,
                               lhsHeap = None)
              val s6 = stateConsolidator.consolidate(s5, v3)
              Q(s6, v3)})})}

        e match {
          case wand: ast.MagicWand =>
            consume(s, wand, pve, v)((s1, _, v1) => {
              QL(s1, s1.g, wand, v1)})

          case x: ast.AbstractLocalVar =>
            val chWand = s.g(x).asInstanceOf[MagicWandChunkTerm].chunk
            magicWandSupporter.getMatchingChunk(s.h, chWand, v) match {
              case Some(ch) =>
                QL(s.copy(h = s.h - ch), Store(chWand.bindings), chWand.ghostFreeWand, v)
              case None =>
                Failure(pve dueTo NamedMagicWandChunkNotFound(x))}

          case _ => sys.error(s"Expected a magic wand, but found node $e")}


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

       case _ if    rhs.existsDefined { case t if TriggerGenerator.isForbiddenInTrigger(t) => true }
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
