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
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.{NegativePermission, QPAssertionNotInjective}

trait ProductionRules extends SymbolicExecutionRules {

  /** Produce assertion `a` into state `s`.
    *
    * @param s The state to produce the assertion into.
    * @param sf The heap snapshot determining the values of the produced partial heap.
    * @param a The assertion to produce.
    * @param pve The error to report in case the production fails.
    * @param Q The continuation to invoke if the production succeeded, with the state
    *          resulting from the production as argument.
    * @return The result of the continuation.
    */
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError)
             (Q: State => VerificationResult)
             : VerificationResult

  /** Subsequently produces assertions `as` into state `s`.
    *
    * `produces(s, sf, as, _ => pve)` should (not yet tested ...) be equivalent to
    * `produce(s, sf, BigAnd(as), pve)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to produce the assertions into.
    * @param sf The heap snapshots determining the values of the produced partial heaps.
    * @param as The assertions to produce.
    * @param pvef The error to report in case the production fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if producing assertion `as_i` fails.
    * @param Q @see [[produce]]
    * @return @see [[produce]]
    */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError)
              (Q: State => VerificationResult)
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
              pve: PartialVerificationError)
             (Q: State => VerificationResult)
             : VerificationResult =

    produceR(s, sf, a.whenInhaling, pve)(Q)

  /** @inheritdoc */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError)
              (Q: State => VerificationResult)
              : VerificationResult = {
    val v = s.v

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    as.foreach(a => {
      val tlcs = a.whenInhaling.topLevelConjuncts
      val pves = Seq.fill(tlcs.length)(pvef(a))

      allTlcs ++= tlcs
      allPves ++= pves
    })

    produceTlcs(s, sf, allTlcs.result(), allPves.result())(Q)
  }

  private def produceTlcs(s: State,
                          sf: (Sort, Verifier) => Term,
                          as: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError])
                         (Q: State => VerificationResult)
                         : VerificationResult = {
    val v = s.v

    if (as.isEmpty)
      Q(s)
    else {
      val a = as.head.whenInhaling
      val pve = pves.head

      if (as.tail.isEmpty)
        wrappedProduceTlc(s, sf, a, pve)(Q)
      else {
        try {
          val (sf0, sf1) =
            v.snapshotSupporter.createSnapshotPair(s, sf, a, viper.silicon.utils.ast.BigAnd(as.tail), v)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter as) is BigAnd-ed
           *       over and over again.
           */

          wrappedProduceTlc(s, sf0, a, pve)(s1 =>
            produceTlcs(s1, sf1, as.tail, pves.tail)(Q))
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
                       pve: PartialVerificationError)
                      (Q: State => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

    produceTlcs(s, sf, tlcs, pves)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    */
  private def wrappedProduceTlc(s: State,
                                sf: (Sort, Verifier) => Term,
                                a: ast.Exp,
                                pve: PartialVerificationError)
                               (Q: State => VerificationResult)
                               : VerificationResult = {
    val v = s.v

    val sepIdentifier = v.symbExLog.openScope(new ProduceRecord(a, s, v.decider.pcs))
    produceTlc(s, sf, a, pve)(s1 => {
      s1.v.symbExLog.closeScope(sepIdentifier)
      Q(s1)})
  }

  private def produceTlc(s: State,
                         sf: (Sort, Verifier) => Term,
                         a: ast.Exp,
                         pve: PartialVerificationError)
                        (continuation: State => VerificationResult)
                        : VerificationResult = {
    val v = s.v

    v.logger.debug(s"\nPRODUCE ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
    v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))

    val Q: State => VerificationResult = state =>
      continuation(if (state.exhaleExt) state.updateWand(_.copy(reserveHeaps = state.h +: state.reserveHeaps.drop(1))) else state)

    val produced = a match {
      case imp @ ast.Implies(e0, a0) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "produce")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        eval(s, e0, pve)((s1, t0, e0New) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, resetState = false)((s1, QB) =>
            branch(s1.updateSettings(_.copy(parallelizeBranches = false)), t0, (e0, e0New))(
              s2 => produceR(s2.updateSettings(_.copy(parallelizeBranches = s1.parallelizeBranches)), sf, a0, pve)(s3 => {
                s3.v.symbExLog.closeScope(uidImplies)
                QB(s3, null)
              }),
              s2 => {
                s2.v.decider.assume(sf(sorts.Snap, s2.v) === Unit, Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true)))
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
                s2.v.symbExLog.closeScope(uidImplies)
                QB(s2.updateSettings(_.copy(parallelizeBranches = s1.parallelizeBranches)), null)
              })
          )(entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMergeWithoutConsolidation(entry2)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, null)
          })((s, _) => Q(s))
        )

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "produce")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        eval(s, e0, pve)((s1, t0, e0New) =>
          branch(s1, t0, (e0, e0New))(
            s2 => produceR(s2, sf, a0, pve)(s3 => {
              s3.v.symbExLog.closeScope(uidImplies)
              Q(s3)
            }),
            s2 => {
                s2.v.decider.assume(sf(sorts.Snap, s2.v) === Unit, Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true)))
                  /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                   * otherwise. In order words, only make this assumption if `sf` has
                   * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                   */
                s2.v.symbExLog.closeScope(uidImplies)
                Q(s2)
            }))

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "produce")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve)((s1, t0, e0New) =>
          // The type arguments here are Null because there is no need to pass any join data.
          joiner.join[scala.Null, scala.Null](s1, resetState = false)((s1, QB) =>
            branch(s1.updateSettings(_.copy(parallelizeBranches = false)), t0, (e0, e0New))(
              s2 => produceR(s2.updateSettings(_.copy(parallelizeBranches = s1.parallelizeBranches)), sf, a1, pve)(s3 => {
                s3.v.symbExLog.closeScope(uidCondExp)
                QB(s3, null)
              }),
              s2 => produceR(s2.updateSettings(_.copy(parallelizeBranches = s1.parallelizeBranches)), sf, a2, pve)(s3 => {
                s3.v.symbExLog.closeScope(uidCondExp)
                QB(s3, null)
              }))
          )(entries => {
            val s2 = entries match {
              case Seq(entry) => // One branch is dead
                entry.s
              case Seq(entry1, entry2) => // Both branches are alive
                entry1.pathConditionAwareMerge(entry2)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, null)
          })((s, _) => Q(s))
        )

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "produce")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        eval(s, e0, pve)((s1, t0, e0New) =>
          branch(s1, t0, (e0, e0New))(
            s2 => produceR(s2, sf, a1, pve)(s3 => {
              s3.v.symbExLog.closeScope(uidCondExp)
              Q(s3)
            }),
            s2 => produceR(s2, sf, a2, pve)(s3 => {
              s3.v.symbExLog.closeScope(uidCondExp)
              Q(s3)
            })))

      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve)((s1, g1, body) =>
          produceR(s1.copy(g = s1.g + g1), sf, body, pve)(Q))

      case accPred: ast.AccessPredicate =>
        val eArgs = accPred.loc.args(s.program)
        val ePerm = accPred.perm
        val resource = accPred.res(s.program)

        evals(s, eArgs, _ => pve)((s1, tArgs, eArgsNew) =>
          eval(s1, ePerm, pve)((s1a, tPerm, ePermNew) => {
            val v1a = s1a.v
            permissionSupporter.assertNotNegative(s1a, tPerm, ePerm, ePermNew, pve, v1a)((s1b, v2) => {
              val s2 = s1b.copy(constrainableARPs = s.constrainableARPs)
              val snap = sf(v2.snapshotSupporter.optimalSnapshotSort(resource, s2, v2), v2)
              val gain = if (!Verifier.config.unsafeWildcardOptimization() || s2.isPermLocation(resource))
                PermTimes(tPerm, s2.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
              val gainExp = ePermNew.map(p => ast.PermMul(p, s2.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
              v2.heapSupporter.produceSingle(s2, resource, tArgs, eArgsNew, snap, None, gain, gainExp, pve, true, v2)((s3, _v3) => Q(s3))
            })}))


      case qpa@QuantifiedPermissionAssertion(forall, cond, accPred) =>
        val resource = accPred.res(s.program)
        val resAcc = accPred.loc
        val eArgs = resAcc.args(s.program)
        val tFormalArgs = s.getFormalArgVars(resource)
        val eFormalArgs = Option.when(withExp)(s.getFormalArgDecls(resource))
        val ePerm = accPred.perm
        val qid =
          accPred match {
            case ast.FieldAccessPredicate(ast.FieldAccess(_, fld), _) =>
              fld.name
            case ast.PredicateAccessPredicate(ast.PredicateAccess(_, predName), _) =>
              predName
            case w: ast.MagicWand =>
              MagicWandIdentifier(w, s.program).toString
          }
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val s0 = s.copy(functionRecorder = s.functionRecorder.enterQuantifiedExp(qpa))
        evalQuantified(s0, Forall, forall.variables, Seq(cond), ePerm +: eArgs, optTrigger, qid, pve) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((Seq(tPerm, tArgs@_*), permArgs, tTriggers, (auxGlobals, auxNonGlobals), auxExps))) =>
            val v1 = s1.v
            val s1a = s1.copy(constrainableARPs = s.constrainableARPs)
            v1.heapSupporter.produceQuantified(s1a, sf, forall, resource, qvars, qvarExps, tFormalArgs, eFormalArgs, qid, optTrigger, tTriggers, auxGlobals, auxNonGlobals,
              auxExps.map(_._1), auxExps.map(_._2), tCond, eCondNew.map(_.head), tArgs, permArgs.map(_.tail), tPerm, permArgs.map(_.head), pve, NegativePermission(ePerm),
              QPAssertionNotInjective(resAcc), v1)((s2, _v2) => {
              Q(s2.copy(functionRecorder = s2.functionRecorder.leaveQuantifiedExp(qpa)))
            })
          case (s1, _, _, _, _, None) => Q(s1.copy(constrainableARPs = s.constrainableARPs))
        }

      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), s, "valid AST")

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit,
          Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true))) /* TODO: See comment for case ast.Implies above */
        eval(s, a, pve)((s1, t, aNew) => {
          s1.v.decider.assume(t, Option.when(withExp)(a), aNew)
          Q(s1)})
    }

    produced
  }
}
