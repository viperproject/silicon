// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.Config.JoinMode

import scala.collection.mutable
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.logger.records.data.{CondExpRecord, ImpliesRecord, ProduceRecord}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.{NegativePermission, QPAssertionNotInjective}

trait ProductionRules extends SymbolicExecutionRules {

  /** Produce assertion `a` into state `s`.
    *
    * @param s The state to produce the assertion into.
    * @param sf The heap snapshot determining the values of the produced partial heap.
    * @param a The assertion to produce.
    * @param pve The error to report in case the production fails.
    * @param v The verifier to use.
    * @param Q The continuation to invoke if the production succeeded, with the state and
    *          the verifier resulting from the production as arguments.
    * @return The result of the continuation.
    */
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult

  /** Subsequently produces assertions `as` into state `s`.
    *
    * `produces(s, sf, as, _ => pve, v)` should (not yet tested ...) be equivalent to
    * `produce(s, sf, BigAnd(as), pve, v)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to produce the assertions into.
    * @param sf The heap snapshots determining the values of the produced partial heaps.
    * @param as The assertions to produce.
    * @param pvef The error to report in case the production fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if producing assertion `as_i` fails.
    * @param v @see [[produce]]
    * @param Q @see [[produce]]
    * @return @see [[produce]]
    */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Verifier) => VerificationResult)
              : VerificationResult
}

object producer extends ProductionRules {
  import brancher._
  import evaluator._

  /* Overview of and interaction between the different available produce-methods:
   *   - `produce` and `produces` are the entry methods and intended to be called by *clients*
   *     (e.g. from the executor), but *not* by the implementation of the producer itself
   *     (e.g. recursively).
   *   - Produce methods suffixed with `tlc` (or `tlcs`) expect top-level conjuncts as assertions.
   *     The other produce methods therefore split the given assertion(s) into top-level
   *     conjuncts and forward these to `produceTlcs`.
   *   - `produceTlc` implements the actual symbolic execution rules for producing an assertion,
   *     and `produceTlcs` is basically `produceTlc` lifted to a sequence of assertions
   *     (a continuation-aware fold, if you will).
   *   - Certain operations such as logging need to be performed per produced top-level conjunct.
   *     This is implemented by `wrappedProduceTlc`: a wrapper around (or decorator for)
   *     `produceTlc` that performs additional operations before/after invoking `produceTlc`.
   *     `produceTlcs` therefore repeatedly invokes `wrappedProduceTlc` (and not `produceTlc`
   *     directly)
   *   - `produceR` is intended for recursive calls: it takes an assertion, splits it into
   *     top-level conjuncts and uses `produceTlcs` to produce each of them (hence, each assertion
   *     to produce passes `wrappedProduceTlc` before finally reaching `produceTlc`).
   *   - Note that the splitting into top-level conjuncts performed by `produceR` is not redundant,
   *     although the entry methods such as `produce` split assertions as well: if a client needs
   *     to produce `a1 && (b ==> a2 && a3) && a4`, then the entry method will split the assertion
   *     into the sequence `[a1, b ==> a2 && a3, a4]`, and the recursively produced assertion
   *     `a2 && a3` (after having branched over `b`) needs to be split again.
   */

  /** @inheritdoc */
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult =

    produceR(s, sf, a.whenInhaling, pve, v)(Q)

  /** @inheritdoc */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Verifier) => VerificationResult)
              : VerificationResult = {

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    as.foreach(a => {
      val tlcs = a.whenInhaling.topLevelConjuncts
      val pves = Seq.fill(tlcs.length)(pvef(a))

      allTlcs ++= tlcs
      allPves ++= pves
    })

    produceTlcs(s, sf, allTlcs.result(), allPves.result(), v)(Q)
  }

  private def produceTlcs(s: State,
                          sf: (Sort, Verifier) => Term,
                          as: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError],
                          v: Verifier)
                         (Q: (State, Verifier) => VerificationResult)
                         : VerificationResult = {

    if (as.isEmpty)
      Q(s, v)
    else {
      val a = as.head.whenInhaling
      val pve = pves.head

      if (as.tail.isEmpty)
        wrappedProduceTlc(s, sf, a, pve, v)(Q)
      else {
        try {
          val (sf0, sf1) =
            v.snapshotSupporter.createSnapshotPair(s, sf, a, viper.silicon.utils.ast.BigAnd(as.tail), v)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter as) is BigAnd-ed
           *       over and over again.
           */

          wrappedProduceTlc(s, sf0, a, pve, v)((s1, v1) =>
            produceTlcs(s1, sf1, as.tail, pves.tail, v1)(Q))
        } catch {
          // We will get an IllegalArgumentException from createSnapshotPair if sf(...) returns Unit.
          // This should never happen if we're in a reachable state, so here we check for that
          // (without timeout, since there is no fallback) and stop verifying the current branch.
          case _: IllegalArgumentException if v.decider.check(False, Verifier.config.assertTimeout.getOrElse(0)) =>
            Unreachable()
        }

      }
    }
  }

  private def produceR(s: State,
                       sf: (Sort, Verifier) => Term,
                       a: ast.Exp,
                       pve: PartialVerificationError,
                       v: Verifier)
                      (Q: (State, Verifier) => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

    produceTlcs(s, sf, tlcs, pves, v)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    */
  private def wrappedProduceTlc(s: State,
                                sf: (Sort, Verifier) => Term,
                                a: ast.Exp,
                                pve: PartialVerificationError,
                                v: Verifier)
                               (Q: (State, Verifier) => VerificationResult)
                               : VerificationResult = {

    val sepIdentifier = v.symbExLog.openScope(new ProduceRecord(a, s, v.decider.pcs))
    produceTlc(s, sf, a, pve, v)((s1, v1) => {
      v1.symbExLog.closeScope(sepIdentifier)
      Q(s1, v1)})
  }

  private def produceTlc(s: State,
                         sf: (Sort, Verifier) => Term,
                         a: ast.Exp,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (continuation: (State, Verifier) => VerificationResult)
                        : VerificationResult = {

    v.logger.debug(s"\nPRODUCE ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
    v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))

    val Q: (State, Verifier) => VerificationResult = (state, verifier) =>
      continuation(if (state.exhaleExt) state.copy(reserveHeaps = state.h +: state.reserveHeaps.drop(1)) else state, verifier)

    val produced = a match {
      case imp @ ast.Implies(e0, a0) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "produce")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        eval(s, e0, pve, v)((s1, t0, v1) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, v1, resetState = false)((s1, v1, QB) =>
            branch(s1.copy(parallelizeBranches = false), t0, Some(e0), v1)(
              (s2, v2) => produceR(s2.copy(parallelizeBranches = s1.parallelizeBranches), sf, a0, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidImplies)
                QB(s3, null, v3)
              }),
              (s2, v2) => {
                v2.decider.assume(sf(sorts.Snap, v2) === Unit)
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
                v2.symbExLog.closeScope(uidImplies)
                QB(s2.copy(parallelizeBranches = s1.parallelizeBranches), null, v2)
              })
          )(entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMergeWithoutConsolidation(entry2, v1)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, null)
          })((s, _, v) => Q(s, v))
        )

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "produce")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        eval(s, e0, pve, v)((s1, t0, v1) =>
          branch(s1, t0, Some(e0), v1)(
            (s2, v2) => produceR(s2, sf, a0, pve, v2)((s3, v3) => {
              v3.symbExLog.closeScope(uidImplies)
              Q(s3, v3)
            }),
            (s2, v2) => {
                v2.decider.assume(sf(sorts.Snap, v2) === Unit)
                  /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                   * otherwise. In order words, only make this assumption if `sf` has
                   * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                   */
                v2.symbExLog.closeScope(uidImplies)
                Q(s2, v2)
            }))

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "produce")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve, v)((s1, t0, v1) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, v1, resetState = false)((s1, v1, QB) =>
            branch(s1.copy(parallelizeBranches = false), t0, Some(e0), v1)(
              (s2, v2) => produceR(s2.copy(parallelizeBranches = s1.parallelizeBranches), sf, a1, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
                QB(s3, null, v3)
              }),
              (s2, v2) => produceR(s2.copy(parallelizeBranches = s1.parallelizeBranches), sf, a2, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
                QB(s3, null, v3)
              }))
          )(entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMerge(entry2, v1)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, null)
          })((s, _, v) => Q(s, v))
        )

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "produce")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve, v)((s1, t0, v1) =>
          branch(s1, t0, Some(e0), v1)(
            (s2, v2) => produceR(s2, sf, a1, pve, v2)((s3, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, v3)
            }),
            (s2, v2) => produceR(s2, sf, a2, pve, v2)((s3, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, v3)
            })))

      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) =>
          produceR(s1.copy(g = s1.g + g1), sf, body, pve, v1)(Q))

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), perm) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, pve, v2)((s3, v3) => {
              val snap = sf(v3.symbolConverter.toSort(field.typ), v3)
              val gain = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(field))
                PermTimes(tPerm, s3.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s3.permissionScalingFactor)
              if (s3.qpFields.contains(field)) {
                val trigger = (sm: Term) => FieldTrigger(field.name, sm, tRcvr)
                quantifiedChunkSupporter.produceSingleLocation(s3, field, Seq(`?r`), Seq(tRcvr), snap, gain, trigger, v3)(Q)
              } else {
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), snap, gain)
                chunkSupporter.produce(s3, s3.h, ch, v3)((s4, h4, v4) =>
                  Q(s4.copy(h = h4), v4))
              }})))

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), perm) =>
        val predicate = s.program.findPredicate(predicateName)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, perm, pve, v1)((s1a, tPerm, v1a) =>
            permissionSupporter.assertNotNegative(s1a, tPerm, perm, pve, v1a)((s2, v2) => {
              val snap = sf(
                predicate.body.map(v2.snapshotSupporter.optimalSnapshotSort(_, s.program)._1)
                              .getOrElse(sorts.Snap), v2)
              val gain = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(predicate))
                PermTimes(tPerm, s2.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
              if (s2.qpPredicates.contains(predicate)) {
                val formalArgs = s2.predicateFormalVarMap(predicate)
                val trigger = (sm: Term) => PredicateTrigger(predicate.name, sm, tArgs)
                quantifiedChunkSupporter.produceSingleLocation(
                  s2, predicate, formalArgs, tArgs, snap, gain, trigger, v2)(Q)
              } else {
                val snap1 = snap.convert(sorts.Snap)
                val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, snap1, gain)
                chunkSupporter.produce(s2, s2.h, ch, v2)((s3, h3, v3) => {
                  if (Verifier.config.enablePredicateTriggersOnInhale() && s3.functionRecorder == NoopFunctionRecorder
                    && !Verifier.config.disableFunctionUnfoldTrigger()) {
                    v3.decider.assume(App(s3.predicateData(predicate).triggerFunction, snap1 +: tArgs))
                  }
                  Q(s3.copy(h = h3), v3)})
              }})))

      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, s.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        evals(s, bodyVars, _ => pve, v)((s1, args,v1) => {
          val (sm, smValueDef) =
            quantifiedChunkSupporter.singletonSnapshotMap(s1, wand, args, sf(sorts.Snap, v1), v1)
          v1.decider.prover.comment("Definitional axioms for singleton-SM's value")
          val definitionalAxiomMark = v1.decider.setPathConditionMark()
          v1.decider.assumeDefinition(smValueDef)
          val conservedPcs =
            if (s1.recordPcs) (s1.conservedPcs.head :+ v1.decider.pcs.after(definitionalAxiomMark)) +: s1.conservedPcs.tail
            else s1.conservedPcs
          val ch =
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, wand, args, FullPerm, sm, s.program)
          val h2 = s1.h + ch
          val smCache1 = if(s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s1.program))){
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h2, ch.id)
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s1, wand, formalVars, relevantChunks, v1)
            v1.decider.assume(PredicateTrigger(ch.id.toString, smDef1.sm, args))
            smCache1
          } else {
            s1.smCache
          }
          val smDef = SnapshotMapDefinition(wand, sm, Seq(smValueDef), Seq())
          val s2 =
            s1.copy(h = h2,
                    functionRecorder = s1.functionRecorder.recordFvfAndDomain(smDef),
                    smCache = smCache1,
                    conservedPcs = conservedPcs)
          Q(s2, v1)})

      case wand: ast.MagicWand =>
        val snap = sf(sorts.Snap, v)
        magicWandSupporter.createChunk(s, wand, MagicWandSnapshot(snap), pve, v)((s1, chWand, v1) =>
          chunkSupporter.produce(s1, s1.h, chWand, v1)((s2, h2, v2) =>
            Q(s2.copy(h = h2), v2)))

      /* TODO: Initial handling of QPs is identical/very similar in consumer
       *       and producer. Try to unify the code.
       */
      case QuantifiedPermissionAssertion(forall, cond, acc: ast.FieldAccessPredicate) =>
        val qid = acc.loc.field.name
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), Seq(acc.loc.rcv, acc.perm), optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tRcvr, tPerm), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val tSnap = sf(sorts.FieldValueFunction(v1.symbolConverter.toSort(acc.loc.field.typ), acc.loc.field.name), v1)
//            v.decider.assume(PermAtMost(tPerm, FullPerm()))
            quantifiedChunkSupporter.produce(
              s1,
              forall,
              acc.loc.field,
              qvars, Seq(`?r`),
              qid, optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              tCond,
              Seq(tRcvr),
              tSnap,
              tPerm,
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
        }

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
        val predicate = s.program.findPredicate(acc.loc.predicateName)
        val formalVars = s.predicateFormalVarMap(predicate)
        val qid = acc.loc.predicateName
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), Seq(tPerm, tArgs @ _*), tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(s1.predicateSnapMap(predicate), predicate.name), v1)
            quantifiedChunkSupporter.produce(
              s1,
              forall,
              predicate,
              qvars,
              formalVars,
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              tCond,
              tArgs,
              tSnap,
              tPerm,
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
        }

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val qid = MagicWandIdentifier(wand, s.program).toString
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, Seq(tCond), tArgs, tTriggers, (auxGlobals, auxNonGlobals), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(sorts.Snap, qid), v1)
            quantifiedChunkSupporter.produce(
              s1,
              forall,
              wand,
              qvars,
              formalVars,
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              tCond,
              tArgs,
              tSnap,
              FullPerm,
              pve,
              NegativePermission(ast.FullPerm()()),
              QPAssertionNotInjective(wand),
              v1
            )(Q)
        }

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), v, s)

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit) /* TODO: See comment for case ast.Implies above */
        eval(s, a, pve, v)((s1, t, v1) => {
          v1.decider.assume(t)
          Q(s1, v1)})
    }

    produced
  }
}
