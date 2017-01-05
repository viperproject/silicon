/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silver.ast
import viper.silver.verifier.reasons._
import viper.silver.verifier.PartialVerificationError
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier

trait ConsumptionRules extends SymbolicExecutionRules {
  def consume(s: State, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Term, Verifier) => VerificationResult)
             : VerificationResult

  def consumes(s: State,
               a: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Term, Verifier) => VerificationResult)
              : VerificationResult
}

object consumer extends ConsumptionRules with Immutable {
  import brancher._
  import evaluator._

  def consume(s: State, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    consume(s, s.h, a.whenExhaling, pve, v)((s1, h1, snap, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap, v1)})
  }

  def consumes(s: State,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Term, Verifier) => VerificationResult)
              : VerificationResult =

    consumes(s, s.h, as map (_.whenExhaling), pvef, v)((s1, snap1, v1) => {
      val s2 = s1.copy(partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap1, v1)})

  private def consumes(s: State,
                       h: Heap,
                       as: Seq[ast.Exp],
                       pvef: ast.Exp => PartialVerificationError,
                       v: Verifier)
                       (Q: (State, Term, Verifier) => VerificationResult)
                       : VerificationResult =

    /* Note: See the code comment about produce vs. produces in
     * DefaultProducer.produces. The same applies to consume vs. consumes.
     */

    if (as.isEmpty)
      Q(s.copy(h = h), Unit, v)
    else {
      val a = as.head

      if (as.tail.isEmpty)
        consume(s, h, a, pvef(a), v)((s1, h1, snap1, v1) =>
          Q(s.copy(h = h1), snap1, v1))
      else
        consume(s, h, a, pvef(a), v)((s1, h1, snap1, v1) =>
          consumes(s1, h1, as.tail, pvef, v1)((s2, snap2, v2) => {
            Q(s2, Combine(snap1, snap2), v2)}))
    }

  /** Wrapper Method for consume, for logging. See Executor.scala for explanation of analogue. **/
  @inline
  private def consume(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
                     (Q: (State, Heap, Term, Verifier) => VerificationResult)
                     : VerificationResult = {

//    val SEP_identifier = SymbExLogger.currentLog().insert(new ConsumeRecord(φ, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    consume2(s, h, a, pve, v)((s1, h1, snap1, v1) => {
//      SymbExLogger.currentLog().collapse(φ, SEP_identifier)
      Q(s1, h1, snap1, v1)})
  }

  private def consume2(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
                      (Q: (State, Heap, Term, Verifier) => VerificationResult)
                      : VerificationResult = {

    /* ATTENTION: Expressions such as `perm(...)` must be evaluated in-place,
     * i.e. in the partially consumed heap which is denoted by `h` here. The
     * evaluator evaluates such expressions in the heap
     * `context.partiallyConsumedHeap`. Hence, this field must be updated every
     * time permissions have been consumed.
     */

    if (!a.isInstanceOf[ast.And]) {
      v.logger.debug(s"\nCONSUME ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
      v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
      v.logger.debug("h = " + v.stateFormatter.format(h))
      if (s.reserveHeaps.nonEmpty)
        v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
    }

    val consumed = a match {
      case ast.And(a1, a2)
              if !a.isPure || Verifier.config.handlePureConjunctsIndividually() =>

        consume(s, h, a1, pve, v)((s1, h1, snap1, v1) =>
          consume(s1, h1, a2, pve, v1)((s2, h2, snap2, v2) => {
            Q(s2, h2, Combine(snap1, snap2), v2)}))

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
//        val impLog = new GlobalBranchRecord(imp, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]], "consume")
//        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
//        SymbExLogger.currentLog().initializeBranching()

        evaluator.eval(s, e0, pve, v)((s1, t0, v1) => {
//          impLog.finish_cond()
          val branch_res = branch(s1, t0, v1,
            (s2, v2) => consume(s2, h, a0, pve, v2)((s3, h3, snap3, v3) => {
              val res1 = Q(s3, h3, snap3, v3)
//              impLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(impLog)
              res1}),
            (s2, v2) => {
              val res2 = Q(s2, h, Unit, v2)
//              impLog.finish_elsSubs()
              res2})
//          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
//        val gbLog = new GlobalBranchRecord(ite, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]], "consume")
//        val sepIdentifier = SymbExLogger.currentLog().insert(gbLog)
//        SymbExLogger.currentLog().initializeBranching()
        eval(s, e0, pve, v)((s1, t0, v1) => {
//          gbLog.finish_cond()
          val branch_res = branch(s1, t0, v1,
            (s2, v2) => consume(s2, h, a1, pve, v2)((s3, h3, snap3, v3) => {
              val res1 = Q(s3, h3, snap3, v3)
//              gbLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(gbLog)
              res1}),
            (s2, v2) => consume(s2, h, a2, pve, v2)((s3, h3, snap3, v3) => {
              val res2 = Q(s3, h3, snap3, v3)
//              gbLog.finish_elsSubs()
              res2}))
//          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ast.utility.QuantifiedPermissions.QPForall(qvar, cond, rcvr, field, perm, forall, fa) => ???
//        val qid = s"prog.l${viper.silicon.utils.ast.sourceLine(forall)}"
//        evalQuantified(s, Forall, Seq(qvar.localVar), Seq(cond), Seq(rcvr, perm), None, qid, pve, v){
//          case (s1, Seq(tQVar), Seq(tCond), Seq(tRcvr, tPerm), _, Left(tAuxQuantNoTriggers), v1) =>
//            v.decider.assert(s1, Forall(tQVar, Implies(tCond, perms.IsNonNegative(tPerm)), Nil)) {
//              case true =>
//                val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
//                val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
//                val invFct =
//                  quantifiedChunkSupporter.getFreshInverseFunction(tQVar, tRcvr, tCond, tPerm, c1.quantifiedVariables)
//                decider.prover.comment("Nested auxiliary terms")
//                assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars, triggers = invFct.invOfFct.triggers))
//                /* TODO: Can we omit/simplify the injectivity check in certain situations? */
//                val receiverInjective = quantifiedChunkSupporter.injectivityAxiom(Seq(tQVar), tCond, tPerm, Seq(tRcvr))
//                decider.prover.comment("Check receiver injectivity")
//                decider.assert(σ, receiverInjective) {
//                  case true =>
//                    decider.prover.comment("Definitional axioms for inverse functions")
//                    assume(invFct.definitionalAxioms)
//                    val inverseReceiver = invFct(`?r`) // e⁻¹(r)
//                    val loss = PermTimes(tPerm, c1.permissionScalingFactor)
//                    quantifiedChunkSupporter.splitLocations(σ, h, field, Some(tQVar), inverseReceiver, tCond, tRcvr, loss, chunkOrderHeuristics, c1) {
//                      case Some((h1, ch, fvfDef, c2)) =>
//                        val fvfDomain = if (c2.fvfAsSnap) fvfDef.domainDefinitions(invFct) else Seq.empty
//                        decider.prover.comment("Definitional axioms for field value function")
//                        assume(fvfDomain ++ fvfDef.valueDefinitions)
//                        val fr3 = c2.functionRecorder.recordFvfAndDomain(fvfDef, fvfDomain)
//                                                     .recordFieldInv(invFct)
//                        val c3 = c2.copy(functionRecorder = fr3,
//                                         partiallyConsumedHeap = Some(h1))
//                        Q(h1, ch.fvf.convert(sorts.Snap), c3)
//                      case None =>
//                        Failure(pve dueTo InsufficientPermission(fa))}
//                  case false =>
//                    Failure(pve dueTo ReceiverNotInjective(fa))}
//              case false =>
//                Failure(pve dueTo NegativePermission(perm))}}

      case ast.utility.QuantifiedPermissions.QPPForall(qvar, cond, args, predname, loss, forall, predAccPred) => ???
//        val predicate = c.program.findPredicate(predname)
//        val formalVars = c.predicateFormalVarMap(predicate)
//        val qid = s"prog.l${utils.ast.sourceLine(forall)}"
//        //evaluate arguments
//        evalQuantified(σ, Forall, Seq(qvar.localVar), Seq(cond), args ++ Seq(loss) , None, qid, pve, c) {
//          case (Seq(tQVar), Seq(tCond), tArgsGain, _, Left(tAuxQuantNoTriggers), c1) =>
//            val (tArgs, Seq(tLoss)) = tArgsGain.splitAt(args.size)
//            //assert positve permission
//            decider.assert(σ, Forall(tQVar, Implies(tCond, perms.IsNonNegative(tLoss)), Nil)) {
//              case true =>
//                //check injectivity and define inverse function
//                val hints = quantifiedPredicateChunkSupporter.extractHints(Some(tQVar), Some(tCond), tArgs)
//                val chunkOrderHeuristics = quantifiedPredicateChunkSupporter.hintBasedChunkOrderHeuristic(hints)
//                val invFct = quantifiedPredicateChunkSupporter.getFreshInverseFunction(tQVar, predicate, formalVars, tArgs, tCond, tLoss, c1.quantifiedVariables)
//                decider.prover.comment("Nested auxiliary terms")
//                assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars, triggers = invFct.invOfFct.triggers))
//                val isInjective = quantifiedPredicateChunkSupporter.injectivityAxiom(Seq(tQVar), tCond, tLoss, tArgs)
//                decider.prover.comment("Check receiver injectivity")
//                decider.assert(σ, isInjective) {
//                  case true =>
//                    decider.prover.comment("Definitional axioms for inverse functions")
//                    assume(invFct.definitionalAxioms)
//                    val inversePredicate = invFct(formalVars) // e⁻¹(arg1, ..., argn)
//                    //remove permission required
//                    quantifiedPredicateChunkSupporter.splitLocations(σ, h, predicate, Some(tQVar), inversePredicate, formalVars,  tArgs, tCond, PermTimes(tLoss, c1.permissionScalingFactor), chunkOrderHeuristics, c1) {
//                      case Some((h1, ch, psfDef, c2)) =>
//                        val psfDomain = if (c2.psfAsSnap) psfDef.domainDefinitions(invFct) else Seq.empty
//                        decider.prover.comment("Definitional axioms for predicate snap function")
//                       assume(psfDomain ++ psfDef.snapDefinitions)
//                        val fr3 = c2.functionRecorder.recordPsfAndDomain(psfDef, psfDomain)
//                                                     .recordPredInv(invFct)
//                        val c3 = c2.copy(functionRecorder = fr3, partiallyConsumedHeap = Some(h1))
//                          Q(h1, ch.psf.convert(sorts.Snap), c3)
//                      case None =>
//                        Failure(pve dueTo InsufficientPermission(predAccPred.loc))}
//                  case false =>
//                    Failure(pve dueTo ReceiverNotInjective(predAccPred.loc))}
//              case false =>
//                Failure(pve dueTo NegativePermission(loss))}}

      case ast.AccessPredicate(fa @ ast.FieldAccess(eRcvr, field), perm)
              if s.qpFields.contains(field) => ???

//        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
//          eval(σ, perm, pve, c1)((tPerm, c2) => {
//            val hints = quantifiedChunkSupporter.extractHints(None, None, tRcvr)
//            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
//            val loss = PermTimes(tPerm, c2.permissionScalingFactor)
//            quantifiedChunkSupporter.splitSingleLocation(σ, h, field, tRcvr, loss, chunkOrderHeuristics, c2) {
//              case Some((h1, ch, fvfDef, c3)) =>
//                val fvfDomain = if (c3.fvfAsSnap) fvfDef.domainDefinitions else Seq.empty
//                assume(fvfDomain ++ fvfDef.valueDefinitions)
//                val c4 = c3.copy(partiallyConsumedHeap = Some(h1))
//                Q(h1, ch.valueAt(tRcvr), c4)
//              case None => Failure(pve dueTo InsufficientPermission(fa))}}))

      case ast.AccessPredicate(pa @ ast.PredicateAccess(eArgs, predname), perm)
              if s.qpPredicates.contains(Verifier.program.findPredicate(predname)) => ???

//        val predicate = c.program.findPredicate(predname)
//        val formalVars:Seq[Var] = c.predicateFormalVarMap(predicate)
//
//        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
//          eval(σ, perm, pve, c1)((tPerm, c2) => {
//            val hints = quantifiedPredicateChunkSupporter.extractHints(None, None, tArgs)
//            val chunkOrderHeuristics = quantifiedPredicateChunkSupporter.hintBasedChunkOrderHeuristic(hints)
//            //remove requires permission
//            quantifiedPredicateChunkSupporter.splitSingleLocation(σ, h, predicate, tArgs, formalVars, PermTimes(tPerm, c2.permissionScalingFactor), chunkOrderHeuristics, c2) {
//              case Some((h1, ch, psfDef, c3)) =>
//                val psfDomain = if (c3.psfAsSnap) psfDef.domainDefinitions else Seq.empty
//                assume(psfDomain ++ psfDef.snapDefinitions)
//                val c4 = c3.copy(partiallyConsumedHeap = Some(h1))
//                Q(h1, ch.valueAt(tArgs), c4)
//              case None => Failure(pve dueTo InsufficientPermission(pa))}}))

      case let: ast.Let if !let.isPure => ???
//        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) => {
//          val c2 =
//            if (c1.recordEffects)
//              c1.copy(letBoundVars = c1.letBoundVars ++ γ1.values)
//            else
//              c1
//          consume(σ \+ γ1, h, body, pve, c2)(Q)})

      case ast.AccessPredicate(locacc, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccess(s1, locacc, pve, v1)((s2, name, args, v2) =>
            v2.decider.assert(perms.IsNonNegative(tPerm)){
              case true =>
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                chunkSupporter.consume(s2, h, name, args, loss, pve, v2, locacc, Some(a))((s3, h1, snap1, v3) => {
                  val s4 = s3.copy(partiallyConsumedHeap = Some(h1))
                  Q(s4, h1, snap1, v3)})
              case false =>
                Failure(pve dueTo NegativePermission(perm))}))

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a))

      /* Handle wands or wand-typed variables */
      case _ if a.typ == ast.Wand && magicWandSupporter.isDirectWand(a) =>
        ???
//        def QL(s: State, h: Heap, chWand: MagicWandChunk, wand: ast.MagicWand, ve: VerificationError, v: Verifier) = {
//          heuristicsSupporter.tryOperation[Heap, Term](s"consume wand $wand")(σ, h, c)((σ, h, c, QS) => {
//            val hs =
//              if (c.exhaleExt) c.reserveHeaps
//              else Stack(h)
//
//            /* TODO: Consuming a wand chunk, respectively, transferring it if c.exhaleExt
//             *       is true, should be implemented on top of MagicWandSupporter.transfer,
//             *       or even on ChunkSupporter.consume.
//             * TODO: Does context.partiallyConsumedHeap need to be updated after consuming chunks?
//             */
//            magicWandSupporter.doWithMultipleHeaps(hs, c)((h1, c1) =>
//              magicWandSupporter.getMatchingChunk(σ, h1, chWand, c1) match {
//                case someChunk @ Some(ch) => (someChunk, h1 - ch, c1)
//                case _ => (None, h1, c1)
//              }
//            ){case (Some(ch), hs1, c1) =>
//                assert(c1.exhaleExt == c.exhaleExt)
//                if (c.exhaleExt) {
//                  /* transfer: move ch into h = σUsed*/
//                  assert(hs1.size == c.reserveHeaps.size)
//                  val topReserveHeap = hs1.head + ch
//                  QS(h /*+ ch*/, decider.fresh(sorts.Snap), c1.copy(reserveHeaps = topReserveHeap +: hs1.tail))
//                } else {
//                  assert(hs1.size == 1)
//                  assert(c.reserveHeaps == c1.reserveHeaps)
//                  QS(hs1.head, decider.fresh(sorts.Snap), c1)
//                }
//
//              case _ => Failure(ve)}
//          })(Q)
//        }
//
//        φ match {
//          case wand: ast.MagicWand =>
//            magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) => {
//              val ve = pve dueTo MagicWandChunkNotFound(wand)
//              QL(σ, h, chWand, wand, ve, c1)})
//          case v: ast.AbstractLocalVar =>
//            val tWandChunk = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
//            val ve = pve dueTo NamedMagicWandChunkNotFound(v)
//            QL(σ, h, tWandChunk, tWandChunk.ghostFreeWand, ve, c)
//          case _ => sys.error(s"Expected a magic wand, but found node $φ")
//        }

      case ast.PackagingGhostOp(eWand, eIn) =>
        ???
//        assert(c.exhaleExt)
//        assert(c.reserveHeaps.head.values.isEmpty)
//        /** TODO: [[HeuristicsSupporter.heuristicsSupporter.packageWand]]
//          *       Is essentially a copy of the code here. Re-use code to avoid running out of sync!
//          */
//        magicWandSupporter.packageWand(σ, eWand, pve, c)((chWand, c1) => {
//          val hOps = c1.reserveHeaps.head + chWand
//          val c2 = c1.copy(exhaleExt = true,
//                           reserveHeaps = H() +: hOps +: c1.reserveHeaps.tail,
//                           lhsHeap = None)
//          assert(c2.reserveHeaps.length == c.reserveHeaps.length)
//          assert(c2.consumedChunks.length == c.consumedChunks.length)
//          assert(c2.consumedChunks.length == c2.reserveHeaps.length - 1)
//          val σEmp = Σ(σ.γ, Ø, σ.g)
//          consume(σEmp, σEmp.h, eIn, pve, c2)((h3, _, c3) =>
//            Q(h3, decider.fresh(sorts.Snap), c3))})

      case ast.ApplyingGhostOp(eWandOrVar, eIn) =>
        ???
//        val (eWand, eLHSAndWand, γ1) = eWandOrVar match {
//          case _eWand: ast.MagicWand =>
//            (_eWand, ast.And(_eWand.left, _eWand)(_eWand.left.pos, _eWand.left.info), σ.γ)
//          case v: ast.AbstractLocalVar =>
//            val chWand = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
//            val _eWand = chWand.ghostFreeWand
//            (_eWand, ast.And(_eWand.left, _eWand)(v.pos, v.info), Γ(chWand.bindings))
//              /* Note that wand reference v is most likely not bound in tChunk.bindings.
//               * Since wands cannot be recursive, this shouldn't be a problem,
//               * as long as v doesn't need to be looked during
//               * magicWandSupporter.applyingWand (for whatever reason).
//               */
//          case _ => sys.error(s"Expected a magic wand, but found node $φ")
//        }
//
//        heuristicsSupporter.tryOperation[S, H](s"applying $eWand")(σ, h, c)((σ, h, c, QS) => /* TODO: Why is h never used? */
//          magicWandSupporter.applyingWand(σ, γ1, eWand, eLHSAndWand, pve, c)(QS)){case (σ1, h1, c1) =>
//            consume(σ1, h1, eIn, pve, c1)((h4, _, c4) =>
//              Q(h4, decider.fresh(sorts.Snap), c4))}

      case ast.FoldingGhostOp(acc: ast.PredicateAccessPredicate, eIn) =>
        ???
//        heuristicsSupporter.tryOperation[S, H](s"folding $acc")(σ, h, c)((σ, h, c, QS) => /* TODO: Why is h never used? */
//          magicWandSupporter.foldingPredicate(σ, acc, pve, c)(QS)){case (σ1, h1, c1) =>
//            consume(σ1, h1, eIn, pve, c1)((h4, _, c4) =>
//              Q(h4, decider.fresh(sorts.Snap), c4))}

      case ast.UnfoldingGhostOp(acc: ast.PredicateAccessPredicate, eIn) =>
        ???
//        heuristicsSupporter.tryOperation[S, H](s"unfolding $acc")(σ, h, c)((σ, h, c, QS) => /* TODO: Why is h never used? */
//          magicWandSupporter.unfoldingPredicate(σ, acc, pve, c)(QS)){case (σ1, h1, c1) =>
//            consume(σ1, h1, eIn, pve, c1)((h4, _, c4) =>
//              Q(h4, decider.fresh(sorts.Snap), c4))}

      case _ =>
        evalAndAssert(s, a, pve, v)((s1, t, v1) => {
          Q(s1, h, t, v1)
        })
    }

    consumed
  }

  private def evalAndAssert(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
                           (Q: (State, Term, Verifier) => VerificationResult)
                           : VerificationResult = {

    /* It is expected that the partially consumed heap (h in the above implementation of
     * `consume`) has already been assigned to `c.partiallyConsumedHeap`.
     *
     * Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * This is done here already (the evaluator would do it as well) to ensure that the eval
     * heap is compressed by tryOrFail if the assertion fails.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    executionFlowController.tryOrFail(s1, v)((s2, v1, QS, QF) => {
      eval(s2, e, pve, v1)((s3, t, v2) =>
        v2.decider.assert(t) {
          case true =>
            v2.decider.assume(t)
            QS(s3, v2)
          case false =>
            QF(Failure(pve dueTo AssertionFalse(e)))})
    })((s4, v4) => {
      val s5 = s4.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s5, Unit, v4)
    })
  }
}
