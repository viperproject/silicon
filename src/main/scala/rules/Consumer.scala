// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.Config.JoinMode

import scala.collection.mutable
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons._
import viper.silicon.interfaces.VerificationResult
import viper.silicon.logger.records.data.{CondExpRecord, ConsumeRecord, ImpliesRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.utils.ast.BigAnd
import viper.silicon.verifier.Verifier

trait ConsumptionRules extends SymbolicExecutionRules {

  /** Consume assertion `a` from state `s`.
    *
    * @param s The state to consume the assertion from.
    * @param a The assertion to consume.
    * @param returnSnap Whether a snapshot should be returned or not.
    * @param pve The error to report in case the consumption fails.
    * @param v The verifier to use.
    * @param Q The continuation to invoke if the consumption succeeded, with the following
    *          arguments: state (1st argument) and verifier (3rd argument) resulting from the
    *          consumption, and a heap snapshot (2bd argument )representing the values of the
    *          consumed partial heap.
    * @return The result of the continuation.
    */
  def consume(s: State, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Option[Term], Verifier) => VerificationResult)
             : VerificationResult

  /** Subsequently consumes the assertions `as` (from head to tail), starting in state `s`.
    *
    * `consumes(s, as, _ => pve, v)` should (not yet tested ...) be equivalent to
    * `consume(s, BigAnd(as), pve, v)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to consume the assertions from.
    * @param as The assertions to consume.
    * @param returnSnap Whether a snapshot should be returned or not.
    * @param pvef The error to report in case a consumption fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if consuming assertion `as_i` fails.
    * @param v @see [[consume]]
    * @param Q @see [[consume]]
    * @return @see [[consume]]
    */
  def consumes(s: State,
               as: Seq[ast.Exp],
               returnSnap: Boolean,
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[Term], Verifier) => VerificationResult)
              : VerificationResult
}

object consumer extends ConsumptionRules {
  import brancher._
  import evaluator._

  /* See the comment in Producer.scala for an overview of the different produce methods: the
   * different consume methods provided by the consumer work and interact analogously.
   */

  /** @inheritdoc */
  def consume(s: State, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Option[Term], Verifier) => VerificationResult)
             : VerificationResult = {

    consumeR(s, s.h, a.whenExhaling, returnSnap, pve, v)((s1, h1, snap, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap, v1)})
  }

  /** @inheritdoc */
  def consumes(s: State,
               as: Seq[ast.Exp],
               returnSnap: Boolean,
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[Term], Verifier) => VerificationResult)
              : VerificationResult = {

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    as.foreach(a => {
      val tlcs = a.whenExhaling.topLevelConjuncts
      val pves = Seq.fill(tlcs.length)(pvef(a))

      allTlcs ++= tlcs
      allPves ++= pves
    })

    consumeTlcs(s, s.h, allTlcs.result(), returnSnap, allPves.result(), v)((s1, h1, snap1, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap1, v1)
    })
  }

  private def consumeTlcs(s: State,
                          h: Heap,
                          tlcs: Seq[ast.Exp],
                          returnSnap: Boolean,
                          pves: Seq[PartialVerificationError],
                          v: Verifier)
                         (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    if (tlcs.isEmpty)
      Q(s, h, if (returnSnap) Some(Unit) else None, v)
    else {
      val a = tlcs.head
      val pve = pves.head

      if (tlcs.tail.isEmpty)
        wrappedConsumeTlc(s, h, a, returnSnap, pve, v)(Q)
      else
        wrappedConsumeTlc(s, h, a, returnSnap, pve, v)((s1, h1, snap1, v1) => {
          consumeTlcs(s1, h1, tlcs.tail, returnSnap, pves.tail, v1)((s2, h2, snap2, v2) =>

            (snap1, snap2) match {
              case (Some(sn1), Some(sn2)) if returnSnap => Q(s2, h2, Some(Combine(sn1, sn2)), v2)
              case (None, None) if !returnSnap => Q(s2, h2, None, v2)
              case (_, _) =>  sys.error(s"Consume returned unexpected snapshot: ${(returnSnap, (snap1, snap2))}")
            })
        })
    }
  }

  private def consumeR(s: State, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                      (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

    consumeTlcs(s, h, tlcs, returnSnap, pves, v)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    *   - Failure-driven state consolidation
    */
  protected def wrappedConsumeTlc(s: State,
                                  h: Heap,
                                  a: ast.Exp,
                                  returnSnap: Boolean,
                                  pve: PartialVerificationError,
                                  v: Verifier)
                                 (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                 : VerificationResult = {

    /* tryOrFail effects the "main" heap s.h, so we temporarily set the consume-heap h to be the
     * main heap. Note that the main heap is used for evaluating expressions during an ongoing
     * consume.
     */
    val sInit = s.copy(h = h)
    executionFlowController.tryOrFail2[Heap, Option[Term]](sInit, v)((s0, v1, QS) => {
      val h0 = s0.h /* h0 is h, but potentially consolidated */
      val s1 = s0.copy(h = s.h) /* s1 is s, but the retrying flag might be set */

      val sepIdentifier = v1.symbExLog.openScope(new ConsumeRecord(a, s1, v.decider.pcs))

      consumeTlc(s1, h0, a, returnSnap, pve, v1)((s2, h2, snap2, v2) => {
        v2.symbExLog.closeScope(sepIdentifier)
        QS(s2, h2, snap2, v2)})
    })(Q)
  }

  private def consumeTlc(s: State, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
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
      case imp @ ast.Implies(e0, a0) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a0, None, uidImplies, returnSnap, pve, v)(Q)

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        evaluator.eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
            (s2, v2) => consumeR(s2, h, a0, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidImplies)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => {
              v2.symbExLog.closeScope(uidImplies)
              Q(s2, h, if (returnSnap) Some(Unit) else None, v2)
            }))

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a1, Some(a2), uidCondExp, returnSnap, pve, v)(Q)

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
            (s2, v2) => consumeR(s2, h, a1, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => consumeR(s2, h, a2, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            })))

      case accPred: ast.AccessPredicate =>
        val eArgs = accPred.loc.args(s.program)
        val resource = accPred.res(s.program)
        val ePerm = accPred.perm

        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          eval(s1, ePerm, pve, v1)((s1a, tPerm, ePermNew, v1a) =>
            permissionSupporter.assertNotNegative(s1a, tPerm, ePerm, ePermNew, pve, v1a)((s2, v2) => {
              val loss = if (!Verifier.config.unsafeWildcardOptimization() ||
                (resource.isInstanceOf[ast.Location] && s2.permLocations.contains(resource.asInstanceOf[ast.Location])))
                PermTimes(tPerm, s2.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
              val lossExp = ePermNew.map(p => ast.PermMul(p, s2.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
              val s3 = v2.heapSupporter.triggerResourceIfNeeded(s2, accPred.loc, tArgs, eArgsNew, v2)
              v2.heapSupporter.consumeSingle(s3, h, accPred.loc, tArgs, eArgsNew, loss, lossExp, returnSnap, pve, v2)((s4, h4, snap, v4) => {
                val s5 = s4.copy(constrainableARPs = s.constrainableARPs,
                                 partiallyConsumedHeap = Some(h4))
                Q(s5, h4, snap, v4)
              })
            })))

      case QuantifiedPermissionAssertion(forall, cond, accPred) =>
        val resAcc = accPred.loc
        val eArgs = resAcc.args(s.program)
        val ePerm = accPred.perm
        val (qid, insuffReason) =
          accPred match {
            case ast.FieldAccessPredicate(fa@ast.FieldAccess(_, fld), _) =>
              val insuffReason = InsufficientPermission(fa)
              (fld.name, insuffReason)
            case ast.PredicateAccessPredicate(pa@ast.PredicateAccess(_, predName), _) =>
              val insuffReason = InsufficientPermission(pa)
              (predName, insuffReason)
            case w: ast.MagicWand =>
              val insuffReason = MagicWandChunkNotFound(w)
              (MagicWandIdentifier(w, s.program).toString, insuffReason)
          }
        val resource = resAcc.res(s.program)
        val tFormalArgs = s.getFormalArgVars(resource, v)
        val eFormalArgs = Option.when(withExp)(s.getFormalArgDecls(resource))
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), ePerm +: eArgs, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), condNew, Some((Seq(tPerm, tArgs@_*), permArgsNew, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            v1.heapSupporter.consumeQuantified(
              s = s1,
              h = h,
              resource = resource,
              qvars = qvars,
              qvarExps = qvarExps,
              tFormalArgs = tFormalArgs,
              eFormalArgs = eFormalArgs,
              qid = qid,
              optTrigger = optTrigger,
              tTriggers = tTriggers,
              auxGlobals = auxGlobals,
              auxNonGlobals = auxNonGlobals,
              auxGlobalsExp = auxExps.map(_._1),
              auxNonGlobalsExp = auxExps.map(_._2),
              tCond = tCond,
              eCond = condNew.map(_.head),
              tArgs = tArgs,
              eArgs = permArgsNew.map(_.tail),
              tPerm = tPerm,
              ePerm = permArgsNew.map(_.head),
              returnSnap = returnSnap,
              pve = pve,
              negativePermissionReason = NegativePermission(ePerm),
              notInjectiveReason = QPAssertionNotInjective(resAcc),
              insufficientPermissionReason = insuffReason,
              v1)((s2, h2, snap, v2) => Q(s2.copy(constrainableARPs = s.constrainableARPs), h2, snap, v2))
          case (s1, _, _, _, _, None, v1) => Q(s1, h, if (returnSnap) Some(Unit) else None, v1)
        }

      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) => {
          val s2 = s1.copy(g = s1.g + g1)
          consumeR(s2, h, body, returnSnap, pve, v1)(Q)})

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), v, s, "valid AST")

      case _ =>
        evalAndAssert(s, a, returnSnap, pve, v)((s1, t, v1) => {
          Q(s1, h, t, v1)
        })
    }

    consumed
  }

  private def consumeConditionalTlcMoreJoins(s: State, h: Heap, e0: ast.Exp, a1: ast.Exp, a2: Option[ast.Exp], scopeUid: Int,
                                             returnSnap: Boolean,
                                             pve: PartialVerificationError, v: Verifier)
                                            (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                            : VerificationResult = {
    eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
      joiner.join[(Heap, Option[Term]), (Heap, Option[Term])](s1, v1, resetState = false)((s1, v1, QB) => {
        branch(s1.copy(parallelizeBranches = false), t0, (e0, e0New), v1)(
          (s2, v2) =>
            consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a1, returnSnap, pve, v2)((s3, h1, t1, v3) => {
            v3.symbExLog.closeScope(scopeUid)
            QB(s3, (h1, t1), v3)
          }),
          (s2, v2) =>
            a2 match {
              case Some(a2) => consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a2, returnSnap, pve, v2)((s3, h1, t1, v3) => {
                v3.symbExLog.closeScope(scopeUid)
                QB(s3, (h1, t1), v3)
              })
              case None =>
                v2.symbExLog.closeScope(scopeUid)
                QB(s2.copy(parallelizeBranches = s1.parallelizeBranches), (h, if (returnSnap) Some(Unit) else None), v2)
            })
      })(entries => {
        val s2 = entries match {
          case Seq(entry) => // One branch is dead
            (entry.s, entry.data)
          case Seq(entry1, entry2) => // Both branches are alive
            val mergedData = (
              State.mergeHeap(
                entry1.data._1, And(entry1.pathConditions.branchConditions), Option.when(withExp)(BigAnd(entry1.pathConditions.branchConditionExps.map(_._2.get))),
                entry2.data._1, And(entry2.pathConditions.branchConditions), Option.when(withExp)(BigAnd(entry2.pathConditions.branchConditionExps.map(_._2.get))),
              ),
              // Assume that entry1.pcs is inverse of entry2.pcs
              (entry1.data._2, entry2.data._2) match {
                case (Some(t1), Some(t2)) if returnSnap => Some(Ite(And(entry1.pathConditions.branchConditions), t1, t2))
                case (None, None) if !returnSnap => None
                case (_, _) => sys.error(s"Unexpected join data entries: $entries")
              }
            )
            (entry1.pathConditionAwareMergeWithoutConsolidation(entry2, v1), mergedData)
          case _ =>
            sys.error(s"Unexpected join data entries: $entries")
        }
        s2
      })((s4, data, v4) => {
        Q(s4, data._1, data._2, v4)
      })
    )
  }


  private def evalAndAssert(s: State, e: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                           (Q: (State, Option[Term], Verifier) => VerificationResult)
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
      eval(s2, e, pve, v1)((s3, t, eNew, v2) => {
        val termToAssert = t match {
          case Quantification(q, vars, body, trgs, name, isGlob, weight) =>
            val transformed = FunctionPreconditionTransformer.transform(body, s3.program)
            v2.decider.assume(Quantification(q, vars, transformed, trgs, name+"_precondition", isGlob, weight), Option.when(withExp)(e), eNew)
            Quantification(q, vars, Implies(transformed, body), trgs, name, isGlob, weight)
          case _ => t
        }
        v2.decider.assert(termToAssert) {
          case true =>
            v2.decider.assume(t, Option.when(withExp)(e), eNew)
            QS(s3, v2)
          case false =>
            val failure = createFailure(pve dueTo AssertionFalse(e), v2, s3, termToAssert, eNew)
            if (s3.retryLevel == 0 && v2.reportFurtherErrors()){
              v2.decider.assume(t, Option.when(withExp)(e), eNew)
              failure combine QS(s3, v2)
            } else failure}})
    })((s4, v4) => {
      val s5 = s4.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s5, if (returnSnap) Some(Unit) else None, v4)
    })
  }
}
