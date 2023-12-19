// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon

import scala.collection.{immutable, mutable}
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons._
import viper.silicon.interfaces.VerificationResult
import viper.silicon.logger.records.data.{CondExpRecord, ConsumeRecord, ImpliesRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.verifier.Verifier

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

object consumer extends ConsumptionRules {
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

    consumeTlcs(s, s.h, allTlcs.result(), allPves.result(), v, None)((s1, h1, snap1, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap1, v1)
    })
  }

  private def consumeTlcs(s: State,
                          h: Heap,
                          tlcs: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError],
                          v: Verifier,
                          ot: Option[Term])
                         (Q: (State, Heap, Term, Verifier) => VerificationResult)
                         : VerificationResult = {
    if (Verifier.config.maskHeapMode()) {
      val resources = maskHeapSupporter.getResourceSeq(tlcs, s.program)
      consumeTlcsMaskHeap(s, h, tlcs, pves, v, resources, ot)(Q)
    } else {
      internalConsumeTlcs(s, h, tlcs, pves, v, None)(Q)
    }
  }

  def consumeTlcsMaskHeap(s: State,
                          h: Heap,
                          tlcs: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError],
                          v: Verifier,
                          resources: Seq[Any],
                          ot: Option[Term])
                         (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {
    val term = if (ot.isDefined) ot.get else {
      val resMap: Seq[(Any, Term)] = resources.map(r => (r, (if (r.isInstanceOf[ast.Field]) ZeroMask else PredZeroMask)))
      FakeMaskMapTerm(immutable.ListMap(resMap: _*))
    }
    internalConsumeTlcs(s, h, tlcs, pves, v, Some(term))((s2, h2, resMapTerm, v2) => {
      if (ot.isDefined) {
        Q(s2, h2, resMapTerm, v2)
      } else {
        val resMap = resMapTerm.asInstanceOf[FakeMaskMapTerm].masks

        val heapToUse = if (s.exhaleExt) s2.reserveHeaps.head else h // TODO I'm just guessing
        Q(s2, h2, maskHeapSupporter.convertToSnapshot(resMap, resources, heapToUse, s2, v2.decider), v2)
      }
    })
  }

  private def internalConsumeTlcs(s: State,
                                  h: Heap,
                                  tlcs: Seq[ast.Exp],
                                  pves: Seq[PartialVerificationError],
                                  v: Verifier,
                                  resMap: Option[Term])
                                  (Q: (State, Heap, Term, Verifier) => VerificationResult)
  : VerificationResult = {

    if (tlcs.isEmpty) {
      if (Verifier.config.maskHeapMode())
        Q(s, h, resMap.get, v)
      else
        Q(s, h, Unit, v)
    } else {
      val a = tlcs.head
      val pve = pves.head

      if (tlcs.tail.isEmpty)
        wrappedConsumeTlc(s, h, a, pve, v, resMap)(Q)
      else
        wrappedConsumeTlc(s, h, a, pve, v, resMap)((s1, h1, snap1, v1) => {
          internalConsumeTlcs(s1, h1, tlcs.tail, pves.tail, v1, Some(snap1))((s2, h2, snap2, v2) => {
            if (Verifier.config.maskHeapMode())
              Q(s2, h2, snap2, v2)
            else
              Q(s2, h2, Combine(snap1, snap2), v2)
          })
        })
    }
  }

  private def consumeR(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier, ot: Option[Term] = None)
                      (Q: (State, Heap, Term, Verifier) => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

    consumeTlcs(s, h, tlcs, pves, v, ot)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    *   - Failure-driven state consolidation
    */
  protected def wrappedConsumeTlc(s: State,
                                  h: Heap,
                                  a: ast.Exp,
                                  pve: PartialVerificationError,
                                  v: Verifier,
                                  resMap: Option[Term])
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

      val sepIdentifier = v1.symbExLog.openScope(new ConsumeRecord(a, s1, v.decider.pcs))

      consumeTlc(s1, h0, a, pve, v1, resMap)((s2, h2, snap2, v2) => {
        v2.symbExLog.closeScope(sepIdentifier)
        QS(s2, h2, snap2, v2)})
    })(Q)
  }

  private def consumeTlc(s: State, h: Heap, a: ast.Exp, pve: PartialVerificationError, v: Verifier, resMap: Option[Term])
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
      case imp @ ast.Implies(e0, a0) if !a.isPure && s.moreJoins =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a0, None, uidImplies, pve, v)(Q)

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        evaluator.eval(s, e0, pve, v)((s1, t0, v1) =>
          branch(s1, t0, Some(e0), v1)(
            (s2, v2) => consumeR(s2, h, a0, pve, v2, resMap)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidImplies)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => {
              v2.symbExLog.closeScope(uidImplies)
              Q(s2, h, if (Verifier.config.maskHeapMode()) resMap.get else Unit, v2)
            }))

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure && s.moreJoins =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a1, Some(a2), uidCondExp, pve, v)(Q)

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve, v)((s1, t0, v1) =>
          branch(s1, t0, Some(e0), v1)(
            (s2, v2) => consumeR(s2, h, a1, pve, v2, resMap)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => consumeR(s2, h, a2, pve, v2, resMap)((s3, h1, t1, v3) => {
            v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            })))

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
            if (Verifier.config.maskHeapMode()) {
              maskHeapSupporter.consume(
                s = s1,
                h = h,
                resource = field,
                qvars = qvars,
                formalQVars = Seq(`?r`),
                qid = qid.name,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = Seq(tRcvr),
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(acc.perm),
                notInjectiveReason = QPAssertionNotInjective(acc.loc),
                insufficientPermissionReason = InsufficientPermission(acc.loc),
                v1,
                resMap.get.asInstanceOf[FakeMaskMapTerm].masks)(Q)
            } else {
              quantifiedChunkSupporter.consume(
                s = s1,
                h = h,
                resource = field,
                qvars = qvars,
                formalQVars = Seq(`?r`),
                qid = qid.name,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = Seq(tRcvr),
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(acc.perm),
                notInjectiveReason = QPAssertionNotInjective(acc.loc),
                insufficientPermissionReason = InsufficientPermission(acc.loc),
                v1)(Q)
            }
        }

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
        val predicate = s.program.findPredicate(acc.loc.predicateName)
        /* TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
         *       and need to be instantiated in several places. Hence, they need to be known,
         *       which is more complicated if fresh identifiers are used.
         *       At least two options:
         *         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
         *         2. Choose fresh identifiers once; store in and take from state (or from object Verifier)
         */
        val formalVars = s.predicateFormalVarMap(predicate)
        val qid = BasicChunkIdentifier(acc.loc.predicateName)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid.name, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tArgs @ _*), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            if (Verifier.config.maskHeapMode()) {
              maskHeapSupporter.consume(
                s = s1,
                h = h,
                resource = predicate,
                qvars = qvars,
                formalQVars = formalVars,
                qid = qid.name,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = tArgs,
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(acc.perm),
                notInjectiveReason = QPAssertionNotInjective(acc.loc),
                insufficientPermissionReason = InsufficientPermission(acc.loc),
                v1,
                resMap.get.asInstanceOf[FakeMaskMapTerm].masks)(Q)
            } else {
              quantifiedChunkSupporter.consume(
                s = s1,
                h = h,
                resource = predicate,
                qvars = qvars,
                formalQVars = formalVars,
                qid = qid.name,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = tArgs,
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(acc.perm),
                notInjectiveReason = QPAssertionNotInjective(acc.loc),
                insufficientPermissionReason = InsufficientPermission(acc.loc),
                v1)(Q)
            }
        }

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))
        val mwi = MagicWandIdentifier(wand, s.program)
        val qid = mwi.toString
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val ePerm = ast.FullPerm()()
        val tPerm = FullPerm
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), tArgs, tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            if (Verifier.config.maskHeapMode()) {
              maskHeapSupporter.consume(
                s = s1,
                h = h,
                resource = mwi,
                qvars = qvars,
                formalQVars = formalVars,
                qid = qid,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = tArgs,
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(ePerm),
                notInjectiveReason = sys.error("Quantified wand not injective"), /*ReceiverNotInjective(...)*/
                insufficientPermissionReason = MagicWandChunkNotFound(wand),
                v1,
                resMap.get.asInstanceOf[FakeMaskMapTerm].masks)(Q)
            } else {
              quantifiedChunkSupporter.consume(
                s = s1,
                h = h,
                resource = wand,
                qvars = qvars,
                formalQVars = formalVars,
                qid = qid,
                optTrigger = optTrigger,
                tTriggers = tTriggers,
                auxGlobals = auxGlobals,
                auxNonGlobals = auxNonGlobals,
                tCond = tCond,
                tArgs = tArgs,
                tPerm = tPerm,
                pve = pve,
                negativePermissionReason = NegativePermission(ePerm),
                notInjectiveReason = sys.error("Quantified wand not injective"), /*ReceiverNotInjective(...)*/
                insufficientPermissionReason = MagicWandChunkNotFound(wand), /*InsufficientPermission(...)*/
                v1)(Q)
            }
        }

      case ast.AccessPredicate(locAcc: ast.LocationAccess, ePerm)
        if Verifier.config.maskHeapMode() =>
        evalLocationAccess(s, locAcc, pve, v)((s1, _, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            permissionSupporter.assertNotNegative(s2, tPerm, ePerm, pve, v2)((s3, v3) => {
              val loss = PermTimes(tPerm, s3.permissionScalingFactor)
              maskHeapSupporter.consumeSingleLocation(
                s3,
                h,
                Seq(`?r`),
                tArgs,
                locAcc,
                loss,
                pve,
                v3,
                resMap.get.asInstanceOf[FakeMaskMapTerm].masks
              )((s4, h4, snap, v4) => {
                val s5 = s4.copy(constrainableARPs = s1.constrainableARPs,
                  partiallyConsumedHeap = Some(h4))
                Q(s5, h4, snap, v4)
              })
            })
          }))

      case ast.AccessPredicate(loc @ ast.FieldAccess(eRcvr, field), ePerm)
              if s.qpFields.contains(field) =>

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            val s2p = if (s2.heapDependentTriggers.contains(field)){
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s2.h, BasicChunkIdentifier(field.name))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, field, Seq(`?r`), relevantChunks, v2)
              v2.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr))
              //            v2.decider.assume(PermAtMost(tPerm, FullPerm()))
              s2.copy(smCache = smCache1)
            } else {
              s2
            }
            val loss = PermTimes(tPerm, s2.permissionScalingFactor)
            quantifiedChunkSupporter.consumeSingleLocation(
              s2p,
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
              if s.qpPredicates.contains(s.program.findPredicate(predname)) =>

        val predicate = s.program.findPredicate(predname)
        val formalVars = s.predicateFormalVarMap(predicate)

        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            val s2p = if (s2.heapDependentTriggers.contains(predicate)){
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s.h, BasicChunkIdentifier(predname))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v2)
              v2.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs))
              s2.copy(smCache = smCache1)
            } else {
              s2
            }

            val loss = PermTimes(tPerm, s2.permissionScalingFactor)
            quantifiedChunkSupporter.consumeSingleLocation(
              s2p,
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
          consumeR(s2, h, body, pve, v1, resMap)(Q)})

      case ast.AccessPredicate(locacc: ast.LocationAccess, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccess(s1, locacc, pve, v1)((s2, _, tArgs, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
              val resource = locacc.res(s.program)
              val loss = PermTimes(tPerm, s3.permissionScalingFactor)
              val ve = pve dueTo InsufficientPermission(locacc)
              val description = s"consume ${a.pos}: $a"
              chunkSupporter.consume(s3, h, resource, tArgs, loss, ve, v3, description)((s4, h1, snap1, v4) => {
                val s5 = s4.copy(partiallyConsumedHeap = Some(h1),
                                 constrainableARPs = s.constrainableARPs)
                Q(s5, h1, snap1, v4)})})))

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), v, s)

      /* Handle wands */
      case wand: ast.MagicWand if Verifier.config.maskHeapMode() =>
        magicWandSupporter.evaluateWandArguments(s, wand, pve, v)((s1, tArgs, v1) => {
          val ident = MagicWandIdentifier(wand, s.program)
          val (h1, _) = maskHeapSupporter.findOrCreateMaskHeapChunk(s1.h, ident, v1)
          val s2 = s1.copy(h = h1)
          maskHeapSupporter.consumeSingleLocation(s2, h1, Seq(`?r`), tArgs, wand, FullPerm, pve, v1, resMap.get.asInstanceOf[FakeMaskMapTerm].masks)(Q)
        })

      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, s.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))

        evals(s, bodyVars, _ => pve, v)((s1, tArgs, v1) => {
          val s1p = if (s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s.program))){
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s1.h, MagicWandIdentifier(wand, s.program))
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s1, wand, formalVars, relevantChunks, v1)
            v1.decider.assume(PredicateTrigger(MagicWandIdentifier(wand, s.program).toString, smDef1.sm, tArgs))
            s1.copy(smCache = smCache1)
          } else {
            s1
          }
          val loss = PermTimes(FullPerm, s1.permissionScalingFactor)
          quantifiedChunkSupporter.consumeSingleLocation(
            s1p,
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
          chunkSupporter.consume(s1, h, wand, tArgs, FullPerm, ve, v1, description)(Q)
        })

      case _ =>
        evalAndAssert(s, a, pve, v, resMap)((s1, t, v1) => {
          Q(s1, h, t, v1)
        })
    }

    consumed
  }


  private def consumeConditionalTlcMoreJoins(s: State, h: Heap, e0: ast.Exp, a1: ast.Exp, a2: Option[ast.Exp], scopeUid: Int,
                                             pve: PartialVerificationError, v: Verifier)
                                            (Q: (State, Heap, Term, Verifier) => VerificationResult)
                                            : VerificationResult = {
    eval(s, e0, pve, v)((s1, t0, v1) =>
      joiner.join[(Heap, Term), (Heap, Term)](s1, v1, resetState = false)((s1, v1, QB) => {
        branch(s1.copy(parallelizeBranches = false), t0, Some(e0), v1)(
          (s2, v2) =>
            consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a1, pve, v2)((s3, h1, t1, v3) => {
            v3.symbExLog.closeScope(scopeUid)
            QB(s3, (h1, t1), v3)
          }),
          (s2, v2) =>
            a2 match {
              case Some(a2) => consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a2, pve, v2)((s3, h1, t1, v3) => {
                v3.symbExLog.closeScope(scopeUid)
                QB(s3, (h1, t1), v3)
              })
              case None =>
                v2.symbExLog.closeScope(scopeUid)
                QB(s2.copy(parallelizeBranches = s1.parallelizeBranches), (h, Unit), v2)
            })
      })(entries => {
        val s2 = entries match {
          case Seq(entry) => // One branch is dead
            (entry.s, entry.data)
          case Seq(entry1, entry2) => // Both branches are alive
            val mergedData = (
              State.mergeHeap(
                entry1.data._1, And(entry1.pathConditions.branchConditions),
                entry2.data._1, And(entry2.pathConditions.branchConditions),
              ),
              // Asume that entry1.pcs is inverse of entry2.pcs
              Ite(And(entry1.pathConditions.branchConditions), entry1.data._2, entry2.data._2)
            )
            (entry1.pathConditionAwareMerge(entry2, v1), mergedData)
          case _ =>
            sys.error(s"Unexpected join data entries: $entries")
        }
        s2
      })((s4, data, v4) => {
        Q(s4, data._1, data._2, v4)
      })
    )
  }

  private def evalAndAssert(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier, resMap: Option[Term])
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
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s, v),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    executionFlowController.tryOrFail0(s1, v)((s2, v1, QS) => {
      eval(s2, e, pve, v1)((s3, t, v2) => {
        val termToAssert = t match {
          case Quantification(q, vars, body, trgs, name, isGlob, weight) =>
            val transformed = FunctionPreconditionTransformer.transform(body, s3.program)
            v2.decider.assume(Quantification(q, vars, transformed, trgs, name+"_precondition", isGlob, weight))
            Quantification(q, vars, Implies(transformed, body), trgs, name, isGlob, weight)
          case _ => t
        }
        v2.decider.assert(termToAssert) {
          case true =>
            v2.decider.assume(t)
            QS(s3, v2)
          case false =>
            val failure = createFailure(pve dueTo AssertionFalse(e), v2, s3)
            if (s3.retryLevel == 0 && v2.reportFurtherErrors()){
              v2.decider.assume(t)
              failure combine QS(s3, v2)
            } else failure}})
    })((s4, v4) => {
      val s5 = s4.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s5, if (Verifier.config.maskHeapMode()) resMap.get else Unit, v4)
    })
  }
}
