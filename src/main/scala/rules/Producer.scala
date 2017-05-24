/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state.terms.{App, _}
import viper.silicon.state.{FieldChunk, PredicateChunk, State}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError

import scala.collection.mutable

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

object producer extends ProductionRules with Immutable {
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
        val (sf0, sf1) = createSnapshotPair(s, sf, a, viper.silicon.utils.ast.BigAnd(as.tail), v)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter Ï†s) is BigAnd-ed
           *       over and over again.
           */

        wrappedProduceTlc(s, sf0, a, pve, v)((s1, v1) =>
          produceTlcs(s1, sf1, as.tail, pves.tail, v1)(Q))
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

//    val sepIdentifier = SymbExLogger.currentLog().insert(new ProduceRecord(s, a, decider.pcs, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    produceTlc(s, sf, a, pve, v)((s1, v1) => {
//      SymbExLogger.currentLog().collapse(a, sepIdentifier)
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
      case imp @ ast.Implies(e0, a0) if !a.isPure =>
//        val impLog = new GlobalBranchRecord(imp, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]], "produce")
//        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
//        SymbExLogger.currentLog().initializeBranching()

        eval(s, e0, pve, v)((s1, t0, v1) => {
//          impLog.finish_cond()
          val branch_res = branch(s1, t0, v1,
            (s2, v2) => produceR(s2, sf, a0, pve, v2)((s3, v3) => {
              val res1 = Q(s3, v3)
//              impLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(impLog)
              res1}),
            (s2, v2) => {
              v2.decider.assume(sf(sorts.Snap, v2) === Unit)
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
              val res2 = Q(s2,  v2)
//              impLog.finish_elsSubs()
              res2})
//          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
//        val gbLog = new GlobalBranchRecord(ite, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]], "produce")
//        val sepIdentifier = SymbExLogger.currentLog().insert(gbLog)
//        SymbExLogger.currentLog().initializeBranching()
        eval(s, e0, pve, v)((s1, t0, v1) => {
//          gbLog.finish_cond()
          val branch_res = branch(s1, t0, v1,
            (s2, v2) => produceR(s2, sf, a1, pve, v2)((s3, v3) => {
              val res1 = Q(s3, v3)
//              gbLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(gbLog)
              res1}),
            (s2, v2) => produceR(s2, sf, a2, pve, v2)((s3, v3) => {
              val res2 = Q(s3, v3)
//              gbLog.finish_elsSubs()
              res2}))
//          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) =>
          produceR(s1.copy(g = s1.g + g1), sf, body, pve, v1)(Q))

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), perm) =>
        /* TODO: Verify similar to the code in DefaultExecutor/ast.NewStmt - unify */
        def addNewChunk(s: State, rcvr: Term, snap: Term, p: Term, v: Verifier)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

          if (s.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createSingletonFieldValueFunction(s, field, rcvr, snap, v)
            optFvfDef.foreach(fvfDef => v.decider.assume(fvfDef.valueDefinitions))
            val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(rcvr, field.name, fvf, p)
            val s1 = optFvfDef.fold(s)(fvfDef => {
              val fr1 = s.functionRecorder.recordFvfAndDomain(fvfDef, Seq.empty, s.quantifiedVariables)
              s.copy(functionRecorder = fr1)})
            Q(s1.copy(h = s1.h + ch), v)
          } else {
            val ch = FieldChunk(rcvr, field.name, snap, p)
            chunkSupporter.produce(s, s.h, ch, v)((s1, h1, v1) =>
              Q(s1.copy(h = h1), v1))
          }
        }

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assume(PermAtMost(NoPerm(), tPerm))
            v2.decider.assume(Implies(PermLess(NoPerm(), tPerm), tRcvr !== Null()))
            val snap = sf(v2.symbolConverter.toSort(field.typ), v2)
            val gain = PermTimes(tPerm, s2.permissionScalingFactor)
            addNewChunk(s2, tRcvr, snap, gain, v2)(Q)}))

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), perm) =>
        val predicate = Verifier.program.findPredicate(predicateName)

        def addNewChunk(s: State, args: Seq[Term], snap: Term, p: Term, v: Verifier)
                       (Q: (State, Verifier) => VerificationResult)
                       : VerificationResult = {

          if (s.qpPredicates.contains(predicate)) {
            v.decider.prover.comment("define formalVArgs")
            val formalArgs:Seq[Var] = s.predicateFormalVarMap(predicate)
            v.decider.prover.comment("createPredicateSnapFunction")
            val (psf, optPsfDef) = quantifiedPredicateChunkSupporter.createPredicateSnapFunction(predicate, args, formalArgs, snap, s.predicateSnapMap, v)
            v.decider.prover.comment("assume snapDefinition")
            optPsfDef.foreach(psfDef => v.decider.assume(psfDef.snapDefinitions))
            val ch = quantifiedPredicateChunkSupporter.createSingletonQuantifiedPredicateChunk(args, formalArgs, predicate.name, psf, p)
            Q(s.copy(h = s.h + ch), v)
          } else {
            val snap1 = snap.convert(sorts.Snap)
            val ch = PredicateChunk(predicate.name, args, snap1, p)
            chunkSupporter.produce(s, s.h, ch, v)((s1, h1, v1) => {
              if (Verifier.config.enablePredicateTriggersOnInhale() && s1.functionRecorder == NoopFunctionRecorder)
              v1.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap1 +: args))
              Q(s1.copy(h = h1), v1)
            })
          }
        }

        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assume(PermAtMost(NoPerm(), tPerm))
            val snap = sf(predicate.body.map(getOptimalSnapshotSort(_, Verifier.program, v2)._1).getOrElse(sorts.Snap), v2)
            val gain = PermTimes(tPerm, s2.permissionScalingFactor)
            addNewChunk(s2, tArgs, snap, gain, v2)(Q)}))

      case wand: ast.MagicWand =>
        magicWandSupporter.createChunk(s, wand, pve, v)((s1, chWand, v1) =>
          Q(s1.copy(h = s1.h + chWand), v1))

      case ast.utility.QuantifiedPermissions.QPForall(qvar, cond, rcvr, field, perm, forall, _) =>
        val qid = s"prog.l${viper.silicon.utils.ast.sourceLine(forall)}"
        val optTrigger = if (forall.triggers.isEmpty) None else Some(forall.triggers)
        evalQuantified(s, Forall, Seq(qvar.localVar), Seq(cond), Seq(rcvr, perm), optTrigger, qid, pve, v){
          case (s1, Seq(tQVar), Seq(tCond), Seq(tRcvr, tPerm), _, auxQuantResult, v1) =>
            val snap = sf(sorts.FieldValueFunction(v1.symbolConverter.toSort(field.typ)), v1)
            val additionalInvFctArgs = s1.quantifiedVariables
            val gain = PermTimes(tPerm, s1.permissionScalingFactor)
            val (ch, invFct) = quantifiedChunkSupporter.createQuantifiedFieldChunk(tQVar, tRcvr, field, snap, gain, tCond, additionalInvFctArgs, v1)

            /* [2016-10-26 Malte]
             * The issue described (and solved) in the previous comment is no longer a problem
             * because quantifiers with FVFs in their triggers are rewritten by abstracting over
             * the concrete FVF with a newly added, quantified variable. This allows the prover
             * to instantiate the nesting axiom with any FVF and to get to the nested definitional
             * axioms.
             * The next comment is kept for documentary purposes.
             *
             * [2015-11-13 Malte]
             * Using the trigger of the inv-of-receiver definitional axiom of the new inverse
             * function as the trigger of the auxiliary quantifier seems like a good choice
             * because whenever we need to learn something about the new inverse function,
             * we might be interested in the auxiliary assumptions as well.
             *
             * This choice of triggers, however, might be problematic when quantified field
             * dereference chains, e.g. x.g.f, where access to x.g and to x.g.f is quantified,
             * are used in pure assertions, as witnessed by method test04 in test case
             * quantified permissions/sets/generalised_shape.sil.
             *
             * In such a scenario, the receiver of (x.g).f will be an fvf-lookup, e.g.
             * lookup_g(fvf1, x), but since fvf1 was introduced when evaluating x.g, the
             * definitional axioms will be nested under the quantifier that is triggered by
             * lookup_g(fvf1, x). In particular, the lookup definitional axiom, i.e. the one
             * stating that lookup_g(fvf1, x) == lookup_g(fvf0, x) will be nested.
             *
             * Since we (currently) introduce a new FVF per field dereference, asserting that
             * we have permissions to (x.g).f (e.g. at some later point) will introduce a new
             * FVF fvf2, alongside a definitional axiom stating that
             * lookup_g(fvf2, x) == lookup_g(fvf0, x).
             *
             * In order to prove that we hold permissions to (x.g).f, we would need to
             * instantiate the auxiliary quantifier, but that quantifier is only triggered by
             * lookup_g(fvf1, x).
             *
             * Hence, we do the following: if the only trigger for the auxiliary quantifier is
             * of the shape lookup_g(fvf1, x), then we search the body for the equality
             * lookup_g(fvf1, x) == lookup_g(fvf0, x), and we use lookup_g(fvf0, x) as the
             * trigger. Searching the body is only necessary because, at the current point, we
             * no longer know the relation between fvf1 and fvf0 (it could be preserved, though).
             */

            v1.decider.prover.comment("Nested auxiliary terms")
            auxQuantResult match {
              case Left(tAuxQuantNoTriggers) =>
                /* No explicit triggers were provided and we resort to those from the inverse
                 * function axiom "e⁻ ¹(e(x)) = x" (i.e. from `invOfFct`). Since the trigger
                 * generation code might have added quantified variables to the axiom, we need
                 * to account for that.
                 */
                v1.decider.assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars,
                                                           triggers = invFct.invOfFct.triggers))
              case Right(tAuxQuants) =>
                /* Explicit triggers were provided. */
                v1.decider.assume(tAuxQuants)
            }
            /* TODO: Reconsider choice of triggers */
            val gainNonNeg = Forall(invFct.invOfFct.vars, perms.IsNonNegative(tPerm), invFct.invOfFct.triggers, s"$qid-perm")
            v1.decider.assume(gainNonNeg)
            v1.decider.prover.comment("Definitional axioms for inverse functions")
            v1.decider.assume(invFct.definitionalAxioms)
            val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
            val ch1 = ch.copy(hints = hints)
            /* TODO: Reconsider choice of triggers */
            val tNonNullQuant = quantifiedChunkSupporter.receiverNonNullAxiom(tQVar, tCond, tRcvr, tPerm, v1)
            v1.decider.prover.comment("Receivers are non-null")
            v1.decider.assume(tNonNullQuant)
            val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordFieldInv(invFct))
            Q(s2.copy(h = s2.h + ch1), v1)}

      case ast.utility.QuantifiedPermissions.QPPForall(qvar, cond, args, predname, gain, forall, _) =>
        //create new quantified predicate chunk
        val predicate = Verifier.program.findPredicate(predname)
        val qid = s"prog.l${viper.silicon.utils.ast.sourceLine(forall)}"
        val optTrigger = if (forall.triggers.isEmpty) None else Some(forall.triggers)
        evalQuantified(s, Forall, Seq(qvar.localVar), Seq(cond), args ++ Seq(gain), optTrigger, qid, pve, v) {
          case (s1, Seq(tQVar), Seq(tCond), tArgsGain, _, auxQuantResult, v1) =>
            val (tArgs, Seq(tGain)) = tArgsGain.splitAt(args.size)
            val snap = sf(sorts.PredicateSnapFunction(s1.predicateSnapMap(predicate)), v1)
            val additionalInvFctArgs = s1.quantifiedVariables
            val gain = PermTimes(tGain, s1.permissionScalingFactor)
            val (ch, invFct) = quantifiedPredicateChunkSupporter.createQuantifiedPredicateChunk(tQVar, predicate, s1.predicateFormalVarMap(predicate), tArgs, snap, gain, tCond, additionalInvFctArgs, v1)
            v1.decider.prover.comment("Nested auxiliary terms")
            auxQuantResult match {
              case Left(tAuxQuantNoTriggers) =>
                v1.decider.assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars,
                                                           triggers = invFct.invOfFct.triggers))
              case Right(tAuxQuants) =>
                v1.decider.assume(tAuxQuants)
            }
            /* TODO: Reconsider choice of triggers */
            val gainNonNeg = Forall(invFct.invOfFct.vars, perms.IsNonNegative(tGain), invFct.invOfFct.triggers, s"$qid-perm")
            v1.decider.assume(gainNonNeg)
            v1.decider.prover.comment("Definitional axioms for inverse functions")
            v1.decider.assume(invFct.definitionalAxioms)
            val hints = quantifiedPredicateChunkSupporter.extractHints(Some(tQVar), Some(tCond), tArgs)
            val ch1 = ch.copy(hints = hints)
            val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordPredInv(invFct))
            Q(s2.copy(h = s2.h + ch1), v1)}

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit) /* TODO: See comment for case ast.Implies above */
        eval(s, a, pve, v)((s1, t, v1) => {
          v1.decider.assume(t)
          Q(s1, v1)})
    }

    produced
  }

  /* TODO: Takes a verifier --> either add a continuation that takes a verifier, or only pass the relevant verifier bits in (fresh?)
   *       Probably better: somehow delay the creation of fresh variables and return the fresh-variables-to-declare
   *       to the caller.
   */
  private def getOptimalSnapshotSort(a: ast.Exp, program: ast.Program, v: Verifier, visited: Seq[String] = Nil)
                                    : (Sort, Boolean) =

    a match {
      case _ if a.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(locacc, _) => locacc match {
        case fa: ast.FieldAccess =>
          (v.symbolConverter.toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName)) {
            program.findPredicate(pa.predicateName).body match {
              case None => (sorts.Snap, false)
              case Some(body) => getOptimalSnapshotSort(body, program, v, pa.predicateName +: visited)
            }
          } else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (sorts.Snap, false)
      }

      case ast.Implies(_, a1) =>
        /* a1 must be impure, otherwise the first case would have applied. */
        getOptimalSnapshotSort(a1, program, v, visited)

      case ast.And(a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(a1, a2, () => (sorts.Snap, false), program, visited)

      case ast.CondExp(_, a1, a2) =>
        /* At least one of a1, a2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = getOptimalSnapshotSort(a1, program, v, visited)
          val (s2, isPure2) = getOptimalSnapshotSort(a2, program, v, visited)
          val s = if (s1 == s2) s1 else sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(a1, a2, findCommonSort, program, visited)

      case ast.utility.QuantifiedPermissions.QPForall(_, _, _, field, _, _, _) =>
        (sorts.FieldValueFunction(v.symbolConverter.toSort(field.typ)), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(a1: ast.Exp,
                                             a2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: Seq[String])
                                            : (Sort, Boolean) = {

    if (a1.isPure && a2.isPure) fIfBothPure()
    else (sorts.Snap, false)
  }

  private def mkSnap(a: ast.Exp, program: ast.Program, v: Verifier, visited: Seq[String] = Nil): Term =
    getOptimalSnapshotSort(a, program, v, visited) match {
      case (sorts.Snap, true) => Unit
      case (sort, _) => v.decider.fresh(sort)
    }

  @inline
  private def createSnapshotPair(s: State,
                                 sf: (Sort, Verifier) => Term,
                                 a0: ast.Exp,
                                 a1: ast.Exp,
                                 v: Verifier)
                                : ((Sort, Verifier) => Term, (Sort, Verifier) => Term) = {

    val (snap0, snap1) = createSnapshotPair(s, sf(sorts.Snap, v), a0, a1, v)

    val sf0 = toSf(snap0)
    val sf1 = toSf(snap1)

    (sf0, sf1)
  }

  private def createSnapshotPair(s: State, snap: Term, a0: ast.Exp, a1: ast.Exp, v: Verifier): (Term, Term) = {
    /* [2015-11-17 Malte] If both fresh snapshot terms and first/second datatypes
     * are used, then the overall test suite verifies in 2min 10sec, whereas
     * it takes 2min 20sec when only first/second datatypes are used. Might be
     * worth re-benchmarking from time to time.
     */

    if (s.functionRecorder == NoopFunctionRecorder) {
      val snap0 = mkSnap(a0, Verifier.program, v)
      val snap1 = mkSnap(a1, Verifier.program, v)

      val snapshotEq = (snap, snap0, snap1) match {
        case (Unit, Unit, Unit) => True()
        case (Unit, _, _) => sys.error(s"Unexpected equality between $s and ($snap0, $snap1)")
        case _ => snap === Combine(snap0, snap1)
      }

      v.decider.assume(snapshotEq)

      (snap0, snap1)
    } else {
      val _snap0 = First(snap)
      val _snap1 = Second(snap)

      (_snap0, _snap1)
    }
  }
}
