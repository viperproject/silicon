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
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.logger.records.data.{CondExpRecord, ImpliesRecord, ProduceRecord}
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
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

        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, v1, resetState = false)((s1, v1, QB) =>
            branch(s1.copy(parallelizeBranches = false), t0, (e0, e0New), v1)(
              (s2, v2) => produceR(s2.copy(parallelizeBranches = s1.parallelizeBranches), sf, a0, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidImplies)
                QB(s3, null, v3)
              }),
              (s2, v2) => {
                v2.decider.assume(sf(sorts.Snap, v2) === Unit, Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true)))
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

        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
            (s2, v2) => produceR(s2, sf, a0, pve, v2)((s3, v3) => {
              v3.symbExLog.closeScope(uidImplies)
              Q(s3, v3)
            }),
            (s2, v2) => {
                v2.decider.assume(sf(sorts.Snap, v2) === Unit, Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true)))
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

        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, v1, resetState = false)((s1, v1, QB) =>
            branch(s1.copy(parallelizeBranches = false), t0, (e0, e0New), v1)(
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

        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
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

      case accPred@ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), _) =>
        val perm = accPred.perm
        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvrNew, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, ePermNew, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, ePermNew, pve, v2)((s2a, v3) => {
              val s3 = s2a.copy(constrainableARPs = s.constrainableARPs)
              val snap = sf(v3.snapshotSupporter.optimalSnapshotSort(field, s3, v3), v3)
              val gain = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(field))
                PermTimes(tPerm, s3.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s3.permissionScalingFactor)
              val gainExp = ePermNew.map(p => ast.PermMul(p, s3.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
              if (s3.qpFields.contains(field)) {
                val trigger = (sm: Term) => FieldTrigger(field.name, sm, tRcvr)
                quantifiedChunkSupporter.produceSingleLocation(s3, field, Seq(`?r`), Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)(accPred.pos, accPred.info, accPred.errT))),
                  Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), snap, gain, gainExp, trigger, v3)(Q)
              } else {
                val (debugHeapName, debugLabel) = v3.getDebugOldLabel(s3, accPred.pos)
                val snapExp = Option.when(withExp)(ast.DebugLabelledOld(ast.FieldAccess(eRcvrNew.get, field)(), debugLabel)(accPred.pos, accPred.info, accPred.errT))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), snap, snapExp, gain, gainExp)
                chunkSupporter.produce(s3, s3.h, ch, v3)((s4, h4, v4) => {
                  val s5 = s4.copy(h = h4)
                  val s6 = if (withExp) s5.copy(oldHeaps = s5.oldHeaps + (debugHeapName -> magicWandSupporter.getEvalHeap(s4))) else s5
                  Q(s6, v4)
                })}})))

      case accPred @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), _) =>
        val predicate = s.program.findPredicate(predicateName)
        val perm = accPred.perm
        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          eval(s1, perm, pve, v1)((s1a, tPerm, ePermNew, v1a) =>
            permissionSupporter.assertNotNegative(s1a, tPerm, perm, ePermNew, pve, v1a)((s1b, v2) => {
              val s2 = s1b.copy(constrainableARPs = s.constrainableARPs)
              val snap = sf(v2.snapshotSupporter.optimalSnapshotSort(predicate, s2, v2), v2)
              val gain = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(predicate))
                PermTimes(tPerm, s2.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
              val gainExp = ePermNew.map(p => ast.PermMul(p, s2.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
              if (s2.qpPredicates.contains(predicate)) {
                val formalArgs = s2.predicateFormalVarMap(predicate)
                val trigger = (sm: Term) => PredicateTrigger(predicate.name, sm, tArgs)
                quantifiedChunkSupporter.produceSingleLocation(
                  s2, predicate, formalArgs, Option.when(withExp)(predicate.formalArgs), tArgs, eArgsNew, snap, gain, gainExp, trigger, v2)(Q)
              } else {
                val snap1 = snap.convert(sorts.Snap)
                val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, eArgsNew, snap1, None, gain, gainExp)
                chunkSupporter.produce(s2, s2.h, ch, v2)((s3, h3, v3) => {
                  if (Verifier.config.enablePredicateTriggersOnInhale() && s3.functionRecorder == NoopFunctionRecorder
                    && !Verifier.config.disableFunctionUnfoldTrigger()) {
                    val argsString = eArgsNew.mkString(", ")
                    val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}($argsString))", isInternal_ = true))
                    v3.decider.assume(App(s3.predicateData(predicate).triggerFunction, snap1 +: tArgs), debugExp)
                  }
                  Q(s3.copy(h = h3), v3)})
              }})))

      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, s.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
        evals(s, bodyVars, _ => pve, v)((s1, args, bodyVarsNew, v1) => {
          val (sm, smValueDef) =
            quantifiedChunkSupporter.singletonSnapshotMap(s1, wand, args, sf(v1.snapshotSupporter.optimalSnapshotSort(wand, s1, v1), v1), v1)
          v1.decider.prover.comment("Definitional axioms for singleton-SM's value")
          val definitionalAxiomMark = v1.decider.setPathConditionMark()
          val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-SM's value", true))
          v1.decider.assumeDefinition(smValueDef, debugExp)
          val conservedPcs =
            if (s1.recordPcs) (s1.conservedPcs.head :+ v1.decider.pcs.after(definitionalAxiomMark)) +: s1.conservedPcs.tail
            else s1.conservedPcs
          val ch =
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, formalVarExps, wand, args, bodyVarsNew,
              FullPerm, Option.when(withExp)(ast.FullPerm()(wand.pos, wand.info, wand.errT)), sm, s.program)
          val h2 = s1.h + ch
          val smCache1 = if (s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s1.program))){
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h2, ch.id)
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s1, wand, formalVars, relevantChunks, v1)
            val argsStr = bodyVarsNew.mkString(", ")
            val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${ch.id.toString}($argsStr))", isInternal_ = true))
            v1.decider.assume(PredicateTrigger(ch.id.toString, smDef1.sm, args), debugExp)
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
        val snap = sf(v.snapshotSupporter.optimalSnapshotSort(wand, s, v), v)
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
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((Seq(tRcvr, tPerm), rcvrPerm, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.FieldValueFunction(v1.snapshotSupporter.optimalSnapshotSort(acc.loc.field, s1, v1), acc.loc.field.name), v1)
            val s1a = s1.copy(constrainableARPs = s.constrainableARPs)
            quantifiedChunkSupporter.produce(
              s1a,
              forall,
              acc.loc.field,
              qvars, qvarExps, Seq(`?r`),
              Option.when(withExp)(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())),
              qid, optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              Seq(tRcvr),
              rcvrPerm.map(rp => Seq(rp.head)),
              tSnap,
              tPerm,
              rcvrPerm.map(_(1)),
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1.copy(constrainableARPs = s.constrainableARPs), v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
        val predicate = s.program.findPredicate(acc.loc.predicateName)
        val formalVars = s.predicateFormalVarMap(predicate)
        val formalVarExps = predicate.formalArgs
        val qid = acc.loc.predicateName
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((Seq(tPerm, tArgs @ _*), permArgs, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(s1.predicateSnapMap(predicate), predicate.name), v1)
            val s1a = s1.copy(constrainableARPs = s.constrainableARPs)
            quantifiedChunkSupporter.produce(
              s1a,
              forall,
              predicate,
              qvars,
              qvarExps,
              formalVars,
              Option.when(withExp)(formalVarExps),
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              tArgs,
              permArgs.map(_.tail),
              tSnap,
              tPerm,
              permArgs.map(_.head),
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1.copy(constrainableARPs = s.constrainableARPs), v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val qid = MagicWandIdentifier(wand, s.program).toString
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((tArgs, eArgsNew, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(sorts.Snap, qid), v1)
            quantifiedChunkSupporter.produce(
              s1,
              forall,
              wand,
              qvars,
              qvarExps,
              formalVars,
              formalVarExps,
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              tArgs,
              eArgsNew,
              tSnap,
              FullPerm,
              Option.when(withExp)(ast.FullPerm()()),
              pve,
              NegativePermission(ast.FullPerm()()),
              QPAssertionNotInjective(wand),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1, v1)
        }

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), v, s, "valid AST")

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit,
          Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true))) /* TODO: See comment for case ast.Implies above */
        eval(s, a, pve, v)((s1, t, aNew, v1) => {
          v1.decider.assume(t, Option.when(withExp)(a), aNew)
          Q(s1, v1)})
    }

    produced
  }
}
