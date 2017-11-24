/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import scala.collection.mutable
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons._
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier
import viper.silicon.{ConsumeRecord, GlobalBranchRecord, SymbExLogger}

trait ConsumptionRules extends SymbolicExecutionRules {

  /** Consume assertion `a` from state `s`.
    *
    * @param s The state to consume the assertion from.
    * @param a The assertion to consume.
    * @param pve The error to report in case the consumption fails.
    * @param v The verifier to use.
    * @param Q The continuation to invoke if the consumption succeeded, with the following
    *          arguments: state (1st argument) and verifier (3rd argument) resulting from the
    *          consumption, and a heap snapshot (2bd argument )representing the values of the
    *          consumed partial heap.
    * @return The result of the continuation.
    */
  def consume(s: State, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Term, Verifier) => VerificationResult)
             : VerificationResult

  /** Subsequently consumes the assertions `as` (from head to tail), starting in state `s`.
    *
    * `consumes(s, as, _ => pve, v)` should (not yet tested ...) be equivalent to
    * `consume(s, BigAnd(as), pve, v)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to consume the assertions from.
    * @param as The assertions to consume.
    * @param pvef The error to report in case a consumption fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if consuming assertion `as_i` fails.
    * @param v @see [[consume]]
    * @param Q @see [[consume]]
    * @return @see [[consume]]
    */
  def consumes(s: State,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Term, Verifier) => VerificationResult)
              : VerificationResult
}

object consumer extends ConsumptionRules with Immutable {
  import brancher._
  import evaluator._

  /* See the comment in Producer.scala for an overview of the different produce methods: the
   * different consume methods provided by the consumer work and interact analogously.
   */

  /** @inheritdoc */
  def consume(s: State, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Term, Verifier) => VerificationResult)
             : VerificationResult = {

    consumeR(s, s.h, a.whenExhaling, pve, v)((s1, h1, snap, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap, v1)})
  }

  /** @inheritdoc */
  def consumes(s: State,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Term, Verifier) => VerificationResult)
              : VerificationResult = {

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    as.foreach(a => {
      val tlcs = a.whenExhaling.topLevelConjuncts
      val pves = Seq.fill(tlcs.length)(pvef(a))

      allTlcs ++= tlcs
      allPves ++= pves
    })

    consumeTlcs(s, s.h, allTlcs.result(), allPves.result(), v)((s1, h1, snap1, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap1, v1)
    })
  }

  private def consumeTlcs(s: State,
                          h: Heap,
                          tlcs: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError],
                          v: Verifier)
                         (Q: (State, Heap, Term, Verifier) => VerificationResult)
                         : VerificationResult = {

    if (tlcs.isEmpty)
      Q(s, h, Unit, v)
    else {
      val a = tlcs.head
      val pve = pves.head

      if (tlcs.tail.isEmpty)
        wrappedConsumeTlc(s, h, a, pve, v)(Q)
      else
        wrappedConsumeTlc(s, h, a, pve, v)((s1, h1, snap1, v1) =>
          consumeTlcs(s1, h1, tlcs.tail, pves.tail, v1)((s2, h2, snap2, v2) =>
            Q(s2, h2, Combine(snap1, snap2), v2)))
    }
  }

  private def consumeR(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
                      (Q: (State, Heap, Term, Verifier) => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

    consumeTlcs(s, h, tlcs, pves, v)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    *   - Failure-driven state consolidation
    */
  protected def wrappedConsumeTlc(s: State,
                                  h: Heap,
                                  a: ast.Exp,
                                  pve: PartialVerificationError,
                                  v: Verifier)
                                 (Q: (State, Heap, Term, Verifier) => VerificationResult)
                                 : VerificationResult = {

    /* tryOrFail effects the "main" heap s.h, so we temporarily set the consume-heap h to be the
     * main heap. Note that the main heap is used for evaluating expressions during an ongoing
     * consume.
     */
    val sInit = s.copy(h = h)
    executionFlowController.tryOrFail2[Heap, Term](sInit, v)((s0, v1, QS) => {
      val h0 = s0.h /* h0 is h, but potentially consolidated */
      val s1 = s0.copy(h = s.h) /* s1 is s, but the retrying flag might be set */

      /* TODO: To remove this cast: Add a type argument to the ConsumeRecord.
       *       Globally the types match, but locally the type system does not know.
       */
      val SEP_identifier = SymbExLogger.currentLog().insert(new ConsumeRecord(a, s1, v.decider.pcs))

      consumeTlc(s1, h0, a, pve, v1)((s2, h2, snap2, v2) => {
        SymbExLogger.currentLog().collapse(a, SEP_identifier)
        QS(s2, h2, snap2, v2)})
    })(Q)
  }

  private def consumeTlc(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, Heap, Term, Verifier) => VerificationResult)
                        : VerificationResult = {

    /* ATTENTION: Expressions such as `perm(...)` must be evaluated in-place,
     * i.e. in the partially consumed heap which is denoted by `h` here. The
     * evaluator evaluates such expressions in the heap
     * `context.partiallyConsumedHeap`. Hence, this field must be updated every
     * time permissions have been consumed.
     */

    v.logger.debug(s"\nCONSUME ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
    v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
    v.logger.debug("h = " + v.stateFormatter.format(h))
    if (s.reserveHeaps.nonEmpty)
      v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))

    val consumed = a match {
      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impLog = new GlobalBranchRecord(imp, s, v.decider.pcs, "consume")
        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
        SymbExLogger.currentLog().initializeBranching()

        evaluator.eval(s, e0, pve, v)((s1, t0, v1) => {
          impLog.finish_cond()
          val branch_res =
            branch(s1, t0, v1)(
              (s2, v2) => consumeR(s2, h, a0, pve, v2)((s3, h3, snap3, v3) => {
                val res1 = Q(s3, h3, snap3, v3)
                impLog.finish_thnSubs()
                SymbExLogger.currentLog().prepareOtherBranch(impLog)
                res1}),
              (s2, v2) => {
                val res2 = Q(s2, h, Unit, v2)
                impLog.finish_elsSubs()
                res2})
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
        val gbLog = new GlobalBranchRecord(ite, s, v.decider.pcs, "consume")
        val sepIdentifier = SymbExLogger.currentLog().insert(gbLog)
        SymbExLogger.currentLog().initializeBranching()
        eval(s, e0, pve, v)((s1, t0, v1) => {
          gbLog.finish_cond()
          val branch_res =
            branch(s1, t0, v1)(
              (s2, v2) => consumeR(s2, h, a1, pve, v2)((s3, h3, snap3, v3) => {
                val res1 = Q(s3, h3, snap3, v3)
                gbLog.finish_thnSubs()
                SymbExLogger.currentLog().prepareOtherBranch(gbLog)
                res1}),
              (s2, v2) => consumeR(s2, h, a2, pve, v2)((s3, h3, snap3, v3) => {
                val res2 = Q(s3, h3, snap3, v3)
                gbLog.finish_elsSubs()
                res2}))
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.FieldAccessPredicate) if s.exhaleExt =>
        val field = acc.loc.field
        val qid = BasicChunkIdentifier(acc.loc.field.name)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), Seq(acc.perm, acc.loc.rcv), optTrigger, qid.name, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tRcvr), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val inverseFunctions =
              quantifiedChunkSupporter.getFreshInverseFunctions(
                qvars,
                And(tCond, IsPositive(tPerm)),
                Seq(tRcvr),
                Seq(`?r`),
                s1.relevantQuantifiedVariables(Seq(tRcvr)),
                optTrigger.map(_ => tTriggers),
                qid.name,
                v1)
            val (effectiveTriggers, effectiveTriggersQVars) =
              optTrigger match {
                case Some(_) =>
                  /* Explicit triggers were provided */
                  (tTriggers, qvars)
                case None =>
                  /* No explicit triggers were provided and we resort to those from the inverse
                   * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                   * Note that the trigger generation code might have added quantified variables
                   * to that axiom.
                   */
                  (inverseFunctions.axiomInversesOfInvertibles.triggers,
                    inverseFunctions.axiomInversesOfInvertibles.vars)
              }
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(auxGlobals)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            optTrigger match {
              case None =>
                /* No explicit triggers provided */
                v1.decider.assume(
                  auxNonGlobals.map(_.copy(
                    vars = effectiveTriggersQVars,
                    triggers = effectiveTriggers)))
              case Some(x) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(auxNonGlobals)
            }
            v1.decider.assert(Forall(qvars, Implies(tCond, perms.IsNonNegative(tPerm)), Nil)) {
              case true =>
                val hints = quantifiedChunkSupporter.extractHints(Some(tCond), Seq(tRcvr))
                val chunkOrderHeuristics =
                  quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                val loss = PermTimes(tPerm, s1.permissionScalingFactor)
                /* TODO: Can we omit/simplify the injectivity check in certain situations? */
                val receiverInjectivityCheck =
                  quantifiedChunkSupporter.injectivityAxiom(
                    qvars     = qvars,
                    condition = tCond,
                    perms     = tPerm,
                    arguments = Seq(tRcvr),
                    triggers  = Nil,
                    qidPrefix = qid.name)
                v1.decider.prover.comment("Check receiver injectivity")
                v1.decider.assert(receiverInjectivityCheck) {
                  case true =>
                    v1.decider.prover.comment("Definitional axioms for inverse functions")
                    v1.decider.assume(inverseFunctions.definitionalAxioms)
                    val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(`?r`)
                    val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
                    val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
                    magicWandSupporter.transfer[QuantifiedBasicChunk](s1, lossOfInvOfLoc, Failure(pve dueTo InsufficientPermission(acc.loc)), v1)((s2, heap, rPerms, v2) => {
                      val (relevantChunks, otherChunks) =
                        quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](heap, BasicChunkIdentifier(field.name))
                      val (result, s3, remainingChunks) = quantifiedChunkSupporter.removePermissions(
                        s2,
                        relevantChunks,
                        Seq(`?r`),
                        condOfInvOfLoc,
                        field,
                        rPerms,
                        chunkOrderHeuristics,
                        v2
                      )
                      val h2 = Heap(remainingChunks ++ otherChunks)
                      val (fvf, fvfValueDefs, optFvfDomainDef) =
                        quantifiedChunkSupporter.summarise(
                          s3,
                          relevantChunks,
                          Seq(`?r`),
                          field,
                          if (s3.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc))) else None,
                          v1)
                      if (s3.smDomainNeeded) {
                        v1.decider.prover.comment("Definitional axioms for SM domain")
                        v1.decider.assume(optFvfDomainDef.get)
                      }
                      v1.decider.prover.comment("Definitional axioms for SM values")
                      v1.decider.assume(fvfValueDefs)
                      val permsTaken = result match {
                        case Complete() => rPerms
                        case Incomplete(remaining) => PermMinus(rPerms, remaining)
                      }
                      val (consumedChunk, _) = quantifiedChunkSupporter.createQuantifiedChunk(
                        qvars,
                        condOfInvOfLoc,
                        acc.loc.field,
                        Seq(tRcvr),
                        permsTaken,
                        Seq(`?r`),
                        fvf,
                        s3.relevantQuantifiedVariables(Seq(tRcvr)),
                        optTrigger.map(_ => tTriggers),
                        qid.name,
                        v2
                      )
                      (result, s3, h2, Some(consumedChunk))
                      })((s3, oCh, v3) =>
                      oCh match {
                        case Some(ch) => Q(s3, s3.h, ch.snapshotMap.convert(sorts.Snap), v3)
                        case _ => Q(s3, s3.h, v3.decider.fresh(sorts.Snap), v3)
                    })
                  case false =>
                    Failure(pve dueTo ReceiverNotInjective(acc.loc))}
              case false =>
                Failure(pve dueTo NegativePermission(acc.perm))}}

      /* TODO: Initial handling of QPs is identical/very similar in consumer
       *       and producer. Try to unify the code.
       */
      case QuantifiedPermissionAssertion(forall, cond, acc: ast.FieldAccessPredicate) =>
        val field = acc.loc.field
        val qid = BasicChunkIdentifier(acc.loc.field.name)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), Seq(acc.perm, acc.loc.rcv), optTrigger, qid.name, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tRcvr), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val inverseFunctions =
              quantifiedChunkSupporter.getFreshInverseFunctions(
                qvars,
                And(tCond, IsPositive(tPerm)),
                Seq(tRcvr),
                Seq(`?r`),
                s1.relevantQuantifiedVariables(Seq(tRcvr)),
                optTrigger.map(_ => tTriggers),
                qid.name,
                v1)
            val (effectiveTriggers, effectiveTriggersQVars) =
              optTrigger match {
                case Some(_) =>
                  /* Explicit triggers were provided */
                  (tTriggers, qvars)
                case None =>
                  /* No explicit triggers were provided and we resort to those from the inverse
                   * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                   * Note that the trigger generation code might have added quantified variables
                   * to that axiom.
                   */
                  (inverseFunctions.axiomInversesOfInvertibles.triggers,
                   inverseFunctions.axiomInversesOfInvertibles.vars)
              }
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(auxGlobals)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            optTrigger match {
              case None =>
                /* No explicit triggers provided */
                v1.decider.assume(
                  auxNonGlobals.map(_.copy(
                    vars = effectiveTriggersQVars,
                    triggers = effectiveTriggers)))
              case Some(x) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(auxNonGlobals)
            }
            v1.decider.assert(Forall(qvars, Implies(tCond, perms.IsNonNegative(tPerm)), Nil)) {
              case true =>
                val hints = quantifiedChunkSupporter.extractHints(Some(tCond), Seq(tRcvr))
                val chunkOrderHeuristics =
                  quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                val loss = PermTimes(tPerm, s1.permissionScalingFactor)
                /* TODO: Can we omit/simplify the injectivity check in certain situations? */
                val receiverInjectivityCheck =
                  quantifiedChunkSupporter.injectivityAxiom(
                    qvars     = qvars,
                    condition = tCond,
                    perms     = tPerm,
                    arguments = Seq(tRcvr),
                    triggers  = Nil,
                    qidPrefix = qid.name)
                v1.decider.prover.comment("Check receiver injectivity")
                v1.decider.assert(receiverInjectivityCheck) {
                  case true =>
                    v1.decider.prover.comment("Definitional axioms for inverse functions")
                    v1.decider.assume(inverseFunctions.definitionalAxioms)
                    val (relevantChunks, otherChunks) =
                      quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](h, BasicChunkIdentifier(field.name))
                    val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(`?r`)
                    val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
                    val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
                    val result = quantifiedChunkSupporter.removePermissions(
                      s1,
                      relevantChunks,
                      Seq(`?r`),
                      condOfInvOfLoc,
                      field,
                      lossOfInvOfLoc,
                      chunkOrderHeuristics,
                      v1
                    )
                    result match {
                      case (Complete(), s2, remainingChunks) =>
                        val h2 = Heap(remainingChunks ++ otherChunks)
                        val (fvf, fvfValueDefs, optFvfDomainDef) =
                          quantifiedChunkSupporter.summarise(
                            s2,
                            relevantChunks,
                            Seq(`?r`),
                            field,
                            if (s2.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc))) else None,
                            v1)
                        if (s2.smDomainNeeded) {
                          v1.decider.prover.comment("Definitional axioms for SM domain")
                          v1.decider.assume(optFvfDomainDef.get)
                        }
                        v1.decider.prover.comment("Definitional axioms for SM values")
                        v1.decider.assume(fvfValueDefs)
                        val fvfDef = SnapshotMapDefinition(field, fvf, fvfValueDefs, optFvfDomainDef.toSeq)
                        val fr3 = s2.functionRecorder.recordFvfAndDomain(fvfDef)
                                                     .recordFieldInv(inverseFunctions)
                        val s3 = s2.copy(functionRecorder = fr3,
                                         partiallyConsumedHeap = Some(h2),
                                         constrainableARPs = s.constrainableARPs)
                        Q(s3, h2, fvf.convert(sorts.Snap), v1)
                      case (Incomplete(_), _, _) =>
                        Failure(pve dueTo InsufficientPermission(acc.loc))}
                  case false =>
                    Failure(pve dueTo ReceiverNotInjective(acc.loc))}
              case false =>
                Failure(pve dueTo NegativePermission(acc.perm))}}

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) if s.exhaleExt =>
        val predicate = Verifier.program.findPredicate(acc.loc.predicateName)
        // TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
        //       and need to be instantiated in several places. Hence, they need to be known,
        //       which is more complicated if fresh identifiers are used.
        //       At least two options:
        //         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
        //         2. Chose fresh identifiers once; store in and take from state (or from object Verifier)
        val formalVars = s.predicateFormalVarMap(predicate)
        val qid = BasicChunkIdentifier(acc.loc.predicateName)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid.name, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tArgs @ _*), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val inverseFunctions =
              quantifiedChunkSupporter.getFreshInverseFunctions(
                qvars,
                And(tCond, IsPositive(tPerm)),
                tArgs,
                formalVars,
                s1.relevantQuantifiedVariables(tArgs),
                optTrigger.map(_ => tTriggers),
                qid.name,
                v1)
            val (effectiveTriggers, effectiveTriggersQVars) =
              optTrigger match {
                case Some(_) =>
                  /* Explicit triggers were provided */
                  (tTriggers, qvars)
                case None =>
                  /* No explicit triggers were provided and we resort to those from the inverse
                   * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                   * Note that the trigger generation code might have added quantified variables
                   * to that axiom.
                   */
                  (inverseFunctions.axiomInversesOfInvertibles.triggers,
                    inverseFunctions.axiomInversesOfInvertibles.vars)
              }
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(auxGlobals)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            optTrigger match {
              case None =>
                /* No explicit triggers provided */
                v1.decider.assume(
                  auxNonGlobals.map(_.copy(
                    vars = effectiveTriggersQVars,
                    triggers = effectiveTriggers)))
              case Some(x) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(auxNonGlobals)
            }
            v1.decider.assert(Forall(qvars, Implies(tCond, perms.IsNonNegative(tPerm)), Nil)) {
              case true =>
                val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
                val chunkOrderHeuristics =
                  quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                val loss = PermTimes(tPerm, s1.permissionScalingFactor)
                /* TODO: Can we omit/simplify the injectivity check in certain situations? */
                val receiverInjectivityCheck =
                  quantifiedChunkSupporter.injectivityAxiom(
                    qvars     = qvars,
                    condition = tCond,
                    perms     = tPerm,
                    arguments = tArgs,
                    triggers  = Nil,
                    qidPrefix = qid.name)
                v1.decider.prover.comment("Check receiver injectivity")
                v1.decider.assert(receiverInjectivityCheck) {
                  case true =>
                    v1.decider.prover.comment("Definitional axioms for inverse functions")
                    v1.decider.assume(inverseFunctions.definitionalAxioms)
                    val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalVars)
                    val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
                    val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
                    magicWandSupporter.transfer[QuantifiedBasicChunk](s1, lossOfInvOfLoc, Failure(pve dueTo InsufficientPermission(acc.loc)), v1)((s2, heap, rPerm, v2) => {
                      val (relevantChunks, otherChunks) =
                      quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](heap, BasicChunkIdentifier(predicate.name))
                      val (result, s3, remainingChunks) = quantifiedChunkSupporter.removePermissions(
                        s2,
                        relevantChunks,
                        formalVars,
                        condOfInvOfLoc,
                        predicate,
                        rPerm,
                        chunkOrderHeuristics,
                        v2
                      )
                      val h2 = Heap(remainingChunks ++ otherChunks)
                      val (fvf, fvfValueDefs, optFvfDomainDef) =
                        quantifiedChunkSupporter.summarise(
                          s3,
                          relevantChunks,
                          formalVars,
                          predicate,
                          if (s3.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc))) else None,
                          v2)
                      if (s3.smDomainNeeded) {
                        v2.decider.prover.comment("Definitional axioms for SM domain")
                        v2.decider.assume(optFvfDomainDef.get)
                      }
                      v2.decider.prover.comment("Definitional axioms for SM values")
                      v2.decider.assume(fvfValueDefs)
                      val permsTaken = result match {
                        case Complete() => rPerm
                        case Incomplete(remaining) => PermMinus(rPerm, remaining)
                      }
                      val (consumedChunk, _) = quantifiedChunkSupporter.createQuantifiedChunk(
                        qvars,
                        condOfInvOfLoc,
                        predicate,
                        tArgs,
                        permsTaken,
                        formalVars,
                        fvf,
                        s3.relevantQuantifiedVariables(tArgs),
                        optTrigger.map(_ => tTriggers),
                        qid.name,
                        v2
                      )
                        (result, s3, h2, Some(consumedChunk))
                      })((s3, oCh, v3) =>
                      oCh match {
                        case Some(ch) => Q(s3, s3.h, ch.snapshotMap.convert(sorts.Snap), v3)
                        case _ => Q(s3, s3.h, v3.decider.fresh(sorts.Snap), v3)
                      })
                  case false =>
                    Failure(pve dueTo ReceiverNotInjective(acc.loc))}
              case false =>
                Failure(pve dueTo NegativePermission(acc.perm))}}

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
        val predicate = Verifier.program.findPredicate(acc.loc.predicateName)
// TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
//       and need to be instantiated in several places. Hence, they need to be known,
//       which is more complicated if fresh identifiers are used.
//       At least two options:
//         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
//         2. Chose fresh identifiers once; store in and take from state (or from object Verifier)
        val formalVars = s.predicateFormalVarMap(predicate)
        val qid = BasicChunkIdentifier(acc.loc.predicateName)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid.name, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tArgs @ _*), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val inverseFunctions =
              quantifiedChunkSupporter.getFreshInverseFunctions(
                qvars,
                And(tCond, IsPositive(tPerm)),
                tArgs,
                formalVars,
                s1.relevantQuantifiedVariables(tArgs),
                optTrigger.map(_ => tTriggers),
                qid.name,
                v1)
            val (effectiveTriggers, effectiveTriggersQVars) =
              optTrigger match {
                case Some(_) =>
                  /* Explicit triggers were provided */
                  (tTriggers, qvars)
                case None =>
                  /* No explicit triggers were provided and we resort to those from the inverse
                   * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                   * Note that the trigger generation code might have added quantified variables
                   * to that axiom.
                   */
                  (inverseFunctions.axiomInversesOfInvertibles.triggers,
                   inverseFunctions.axiomInversesOfInvertibles.vars)
              }
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(auxGlobals)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            optTrigger match {
              case None =>
                /* No explicit triggers provided */
                v1.decider.assume(
                  auxNonGlobals.map(_.copy(
                    vars = effectiveTriggersQVars,
                    triggers = effectiveTriggers)))
              case Some(x) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(auxNonGlobals)
            }
            v1.decider.assert(Forall(qvars, Implies(tCond, perms.IsNonNegative(tPerm)), Nil)) {
              case true =>
                val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
                val chunkOrderHeuristics =
                  quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                val loss = PermTimes(tPerm, s1.permissionScalingFactor)
                /* TODO: Can we omit/simplify the injectivity check in certain situations? */
                val receiverInjectivityCheck =
                  quantifiedChunkSupporter.injectivityAxiom(
                    qvars     = qvars,
                    condition = tCond,
                    perms     = tPerm,
                    arguments = tArgs,
                    triggers  = Nil,
                    qidPrefix = qid.name)
                v1.decider.prover.comment("Check receiver injectivity")
                v1.decider.assert(receiverInjectivityCheck) {
                  case true =>
                    v1.decider.prover.comment("Definitional axioms for inverse functions")
                    v1.decider.assume(inverseFunctions.definitionalAxioms)
                    val (relevantChunks, otherChunks) =
                      quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h, BasicChunkIdentifier(predicate.name))
                    val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalVars)
                    val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
                    val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
                    val result = quantifiedChunkSupporter.removePermissions(
                      s1,
                      relevantChunks,
                      formalVars,
                      condOfInvOfLoc,
                      predicate,
                      lossOfInvOfLoc,
                      chunkOrderHeuristics,
                      v1
                    )
                    result match {
                      case (Complete(), s2, remainingChunks) =>
                        val h2 = Heap(remainingChunks ++ otherChunks)
                        val (fvf, fvfValueDefs, optFvfDomainDef) =
                          quantifiedChunkSupporter.summarise(
                            s2,
                            relevantChunks,
                            formalVars,
                            predicate,
                            if (s2.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc))) else None,
                            v1)
                        if (s2.smDomainNeeded) {
                          v1.decider.prover.comment("Definitional axioms for SM domain")
                          v1.decider.assume(optFvfDomainDef.get)
                        }
                        v1.decider.prover.comment("Definitional axioms for SM values")
                        v1.decider.assume(fvfValueDefs)
                        val fvfDef = SnapshotMapDefinition(predicate, fvf, fvfValueDefs, optFvfDomainDef.toSeq)
                        val fr3 = s2.functionRecorder.recordFvfAndDomain(fvfDef)
                                                     .recordFieldInv(inverseFunctions)
                        val s3 = s2.copy(functionRecorder = fr3,
                                         partiallyConsumedHeap = Some(h2),
                                         constrainableARPs = s.constrainableARPs)
                        Q(s3, h2, fvf.convert(sorts.Snap), v1)
                      case (Incomplete(_), _, _) =>
                        Failure(pve dueTo InsufficientPermission(acc.loc))}
                  case false =>
                    Failure(pve dueTo ReceiverNotInjective(acc.loc))}
              case false =>
                Failure(pve dueTo NegativePermission(acc.perm))}}

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) if s.exhaleExt =>
        // TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
        //       and need to be instantiated in several places. Hence, they need to be known,
        //       which is more complicated if fresh identifiers are used.
        //       At least two options:
        //         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
        //         2. Chose fresh identifiers once; store in and take from state (or from object Verifier)
        val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))
        val qid = MagicWandIdentifier(wand, Verifier.program).toString
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), tArgs, tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val inverseFunctions =
              quantifiedChunkSupporter.getFreshInverseFunctions(
                qvars,
                tCond,
                tArgs,
                formalVars,
                s1.relevantQuantifiedVariables(tArgs),
                optTrigger.map(_ => tTriggers),
                qid,
                v1)
            val (effectiveTriggers, effectiveTriggersQVars) =
              optTrigger match {
                case Some(_) =>
                  /* Explicit triggers were provided */
                  (tTriggers, qvars)
                case None =>
                  /* No explicit triggers were provided and we resort to those from the inverse
                   * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                   * Note that the trigger generation code might have added quantified variables
                   * to that axiom.
                   */
                  (inverseFunctions.axiomInversesOfInvertibles.triggers,
                    inverseFunctions.axiomInversesOfInvertibles.vars)
              }
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(auxGlobals)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            optTrigger match {
              case None =>
                /* No explicit triggers provided */
                v1.decider.assume(
                  auxNonGlobals.map(_.copy(
                    vars = effectiveTriggersQVars,
                    triggers = effectiveTriggers)))
              case Some(x) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(auxNonGlobals)
            }
            val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
            val chunkOrderHeuristics =
              quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            val loss = PermTimes(FullPerm(), s1.permissionScalingFactor)
            /* TODO: Can we omit/simplify the injectivity check in certain situations? */
            val receiverInjectivityCheck =
              quantifiedChunkSupporter.injectivityAxiom(
                qvars     = qvars,
                condition = tCond,
                perms     = FullPerm(),
                arguments = tArgs,
                triggers  = Nil,
                qidPrefix = qid)
            v1.decider.prover.comment("Check receiver injectivity")
            v1.decider.assert(receiverInjectivityCheck) {
              case true =>
                v1.decider.prover.comment("Definitional axioms for inverse functions")
                v1.decider.assume(inverseFunctions.definitionalAxioms)
                val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalVars)
                val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
                val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
                magicWandSupporter.transfer[QuantifiedMagicWandChunk](s1, lossOfInvOfLoc, Failure(pve dueTo MagicWandChunkNotFound(wand)), v1)((s2, heap, rPerm, v2) => {
                val (relevantChunks, otherChunks) =
                  quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](heap, MagicWandIdentifier(wand, Verifier.program))
                val (result, sRes, remainingChunks) = quantifiedChunkSupporter.removePermissions(
                  s2,
                  relevantChunks,
                  formalVars,
                  condOfInvOfLoc,
                  wand,
                  rPerm,
                  chunkOrderHeuristics,
                  v1
                )
                  val h2 = Heap(remainingChunks ++ otherChunks)
                  val (fvf, fvfValueDefs, optFvfDomainDef) =
                    quantifiedChunkSupporter.summarise(
                      sRes,
                      relevantChunks,
                      formalVars,
                      wand,
                      if (sRes.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(rPerm))) else None,
                      v2)
                  if (sRes.smDomainNeeded) {
                    v2.decider.prover.comment("Definitional axioms for SM domain")
                    v2.decider.assume(optFvfDomainDef.get)
                  }
                  v2.decider.prover.comment("Definitional axioms for SM values")
                  v2.decider.assume(fvfValueDefs)
                  val permsTaken = result match {
                    case Complete() => rPerm
                    case Incomplete(remaining) => PermMinus(rPerm, remaining)
                  }
                  val (consumedChunk, _) = quantifiedChunkSupporter.createQuantifiedChunk(
                    qvars,
                    condOfInvOfLoc,
                    wand,
                    tArgs,
                    permsTaken,
                    formalVars,
                    fvf,
                    sRes.relevantQuantifiedVariables(tArgs),
                    optTrigger.map(_ => tTriggers),
                    qid,
                    v2
                  )
                  (result, sRes, h2, Some(consumedChunk.asInstanceOf[QuantifiedMagicWandChunk]))})((s3, oCh, v3) =>
                  oCh match {
                    case Some(ch) => Q(s3, s3.h, ch.snapshotMap.convert(sorts.Snap), v3)
                    case _ => Q(s3, s3.h, v3.decider.fresh(sorts.Snap), v3)
                  })
              case false =>
                Failure(pve dueTo MagicWandChunkNotFound(wand))}}

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        // TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
        //       and need to be instantiated in several places. Hence, they need to be known,
        //       which is more complicated if fresh identifiers are used.
        //       At least two options:
        //         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
        //         2. Chose fresh identifiers once; store in and take from state (or from object Verifier)
        val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))
        val qid = MagicWandIdentifier(wand, Verifier.program).toString
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), tArgs, tTriggers, (auxGlobals, auxNonGlobals), v1) =>
          val inverseFunctions =
            quantifiedChunkSupporter.getFreshInverseFunctions(
              qvars,
              tCond,
              tArgs,
              formalVars,
              s1.relevantQuantifiedVariables(tArgs),
              optTrigger.map(_ => tTriggers),
              qid,
              v1)
          val (effectiveTriggers, effectiveTriggersQVars) =
            optTrigger match {
              case Some(_) =>
                /* Explicit triggers were provided */
                (tTriggers, qvars)
              case None =>
                /* No explicit triggers were provided and we resort to those from the inverse
                 * function axiom inv-of-rcvr, i.e. from `inv(e(x)) = x`.
                 * Note that the trigger generation code might have added quantified variables
                 * to that axiom.
                 */
                (inverseFunctions.axiomInversesOfInvertibles.triggers,
                  inverseFunctions.axiomInversesOfInvertibles.vars)
            }
          v1.decider.prover.comment("Nested auxiliary terms: globals")
          v1.decider.assume(auxGlobals)
          v1.decider.prover.comment("Nested auxiliary terms: non-globals")
          optTrigger match {
            case None =>
              /* No explicit triggers provided */
              v1.decider.assume(
                auxNonGlobals.map(_.copy(
                  vars = effectiveTriggersQVars,
                  triggers = effectiveTriggers)))
            case Some(x) =>
              /* Explicit triggers were provided. */
              v1.decider.assume(auxNonGlobals)
          }
          val hints = quantifiedChunkSupporter.extractHints(Some(tCond), tArgs)
          val chunkOrderHeuristics =
            quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
          val loss = PermTimes(FullPerm(), s1.permissionScalingFactor)
          /* TODO: Can we omit/simplify the injectivity check in certain situations? */
          val receiverInjectivityCheck =
            quantifiedChunkSupporter.injectivityAxiom(
              qvars     = qvars,
              condition = tCond,
              perms     = FullPerm(),
              arguments = tArgs,
              triggers  = Nil,
              qidPrefix = qid)
          v1.decider.prover.comment("Check receiver injectivity")
          v1.decider.assert(receiverInjectivityCheck) {
            case true =>
              v1.decider.prover.comment("Definitional axioms for inverse functions")
              v1.decider.assume(inverseFunctions.definitionalAxioms)
              val (relevantChunks, otherChunks) =
                quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h, MagicWandIdentifier(wand, Verifier.program))
              val qvarsToInvOfLoc = inverseFunctions.qvarsToInversesOf(formalVars)
              val condOfInvOfLoc = tCond.replace(qvarsToInvOfLoc)
              val lossOfInvOfLoc = loss.replace(qvarsToInvOfLoc)
              val result = quantifiedChunkSupporter.removePermissions(
                s1,
                relevantChunks,
                formalVars,
                condOfInvOfLoc,
                wand,
                lossOfInvOfLoc,
                chunkOrderHeuristics,
                v1
              )
              result match {
                case (Complete(), s2, remainingChunks) =>
                  val h2 = Heap(remainingChunks ++ otherChunks)
                  val (fvf, fvfValueDefs, optFvfDomainDef) =
                    quantifiedChunkSupporter.summarise(
                      s2,
                      relevantChunks,
                      formalVars,
                      wand,
                      if (s2.smDomainNeeded) Some(And(condOfInvOfLoc, IsPositive(lossOfInvOfLoc))) else None,
                      v1)
                  if (s2.smDomainNeeded) {
                    v1.decider.prover.comment("Definitional axioms for SM domain")
                    v1.decider.assume(optFvfDomainDef.get)
                  }
                  v1.decider.prover.comment("Definitional axioms for SM values")
                  v1.decider.assume(fvfValueDefs)
                  val fvfDef = SnapshotMapDefinition(wand, fvf, fvfValueDefs, optFvfDomainDef.toSeq)
                  val fr3 = s2.functionRecorder.recordFvfAndDomain(fvfDef)
                              .recordFieldInv(inverseFunctions)
                  val s3 = s2.copy(functionRecorder = fr3,
                                   partiallyConsumedHeap = Some(h2),
                                   constrainableARPs = s.constrainableARPs)
                  Q(s3, h2, fvf.convert(sorts.Snap), v1)
                case (Incomplete(_), _, _) =>
                  Failure(pve dueTo MagicWandChunkNotFound(wand))}
            case false =>
              Failure(pve dueTo MagicWandChunkNotFound(wand))}}


      case ast.AccessPredicate(loc @ ast.FieldAccess(eRcvr, field), ePerm)
              if s.qpFields.contains(field) =>

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            val loss = PermTimes(tPerm, s2.permissionScalingFactor)
            quantifiedChunkSupporter.consumeSingleLocation(
              s2,
              h,
              Seq(`?r`),
              Seq(tRcvr),
              loc,
              loss,
              None,
              pve,
              v2
            )((s3, h3, snap, v3) => {
              val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                               partiallyConsumedHeap = Some(h3))
              Q(s4, h3, snap, v3)})}))

      case ast.AccessPredicate(loc @ ast.PredicateAccess(eArgs, predname), ePerm)
              if s.qpPredicates.contains(Verifier.program.findPredicate(predname)) =>

        val predicate = Verifier.program.findPredicate(predname)
        val formalVars = s.predicateFormalVarMap(predicate)

        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            val loss = PermTimes(tPerm, s2.permissionScalingFactor)
            quantifiedChunkSupporter.consumeSingleLocation(
              s2,
              h,
              formalVars,
              tArgs,
              loc,
              loss,
              None,
              pve,
              v2
            )((s3, h3, snap, v3) => {
              val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                               partiallyConsumedHeap = Some(h3))
              Q(s4, h3, snap, v3)})}))

      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) => {
          val s2 = s1.copy(g = s1.g + g1)
          consumeR(s2, h, body, pve, v1)(Q)})

      case ast.AccessPredicate(locacc, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccess(s1, locacc, pve, v1)((s2, name, tArgs, v2) =>
            v2.decider.assert(perms.IsNonNegative(tPerm)){
              case true =>
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                val ve = pve dueTo InsufficientPermission(locacc)
                val description = s"consume ${a.pos}: $a"
                chunkSupporter.consume(s2, h, BasicChunkIdentifier(name), tArgs, loss, ve, v2, description)((s3, h1, snap1, v3) => {
                  val s4 = s3.copy(partiallyConsumedHeap = Some(h1),
                                   constrainableARPs = s.constrainableARPs)
                  Q(s4, h1, snap1, v3)})
              case false =>
                Failure(pve dueTo NegativePermission(perm))}))

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a))

      /* Handle wands */
      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, Verifier.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))

        evals(s, bodyVars, _ => pve, v)((s1, tArgs, v1) => {
          val loss = PermTimes(FullPerm(), s1.permissionScalingFactor)
          quantifiedChunkSupporter.consumeSingleLocation(
            s1,
            h,
            formalVars,
            tArgs,
            wand,
            loss,
            None,
            pve,
            v1
          )((s3, h3, snap, v3) => {
            val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                             partiallyConsumedHeap = Some(h3))
            Q(s4, h3, snap, v3)})})

      case wand: ast.MagicWand =>
        magicWandSupporter.evaluateWandArguments(s, wand, pve, v)((s1, tArgs, v1) => {
          val ve = pve dueTo MagicWandChunkNotFound(wand)
          val description = s"consume wand $wand"
          chunkSupporter.consume(s1, h, MagicWandIdentifier(wand, Verifier.program), tArgs, FullPerm(), ve, v1, description)(Q)
        })

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
     * heap is consolidated by tryOrFail if the assertion fails.
     * The latter is also the reason for wrapping the assertion check in a tryOrFail block:
     * the tryOrFail that wraps the consumption of each top-level conjunct would not consolidate
     * the right heap.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    executionFlowController.tryOrFail0(s1, v)((s2, v1, QS) => {
      eval(s2, e, pve, v1)((s3, t, v2) =>
        v2.decider.assert(t) {
          case true =>
            v2.decider.assume(t)
            QS(s3, v2)
          case false =>
            Failure(pve dueTo AssertionFalse(e))})
    })((s4, v4) => {
      val s5 = s4.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s5, Unit, v4)
    })
  }
}
