/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.state.terms.{App, _}
import viper.silicon.state.{utils => _, _}
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.verifier.Verifier
import viper.silicon.utils.toSf

trait ProductionRules extends SymbolicExecutionRules {
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult

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

  /* TODO: Why not produce into the current heap s.h directly? Because of the magic wand support? */

  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult =

    produce2(s, sf, a.whenInhaling, pve, v)((s1, h, v1) =>
      Q(s1.copy(h = h), v1))

  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Verifier) => VerificationResult)
              : VerificationResult = {

    /* Note: Produces(φs) allows more fine-grained error reporting when compared
     * to produce(BigAnd(φs)) because with produces, each φ in φs can be
     * produced with its own PartialVerificationError. The two differ in
     * behaviour, though, because producing a list of, e.g., preconditions, with
     * produce results in more explicit conjunctions, and thus in more
     * combine-terms, which can affect the snapshot structure of predicates and
     * functions.
     */
    if (as.isEmpty)
      Q(s, v)
    else {
      val a = as.head.whenInhaling

      if (as.tail.isEmpty)
        produce(s, sf, a, pvef(a), v)(Q)
      else {
        val (sf0, sf1) = createSnapshotPair(s, sf, a, viper.silicon.utils.ast.BigAnd(as.tail), v)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter φs) is BigAnd-ed
           *       over and over again.
           */

        produce(s, sf0, a, pvef(a), v)((s1, v1) => {
          produces(s1, sf1, as.tail, pvef, v1)(Q)})
      }
    }
  }

  /** Wrapper Method for produce, for logging. See Executor.scala for explanation of analogue. **/
  @inline
  private def produce2(s: State,
                       sf: (Sort, Verifier) => Term,
                       a: ast.Exp,
                       pve: PartialVerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Verifier) => VerificationResult)
                      : VerificationResult = {

//    val sepIdentifier = SymbExLogger.currentLog().insert(new ProduceRecord(φ, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    produce3(s, sf, a, pve, v)((s1, h1, v1) => {
//      SymbExLogger.currentLog().collapse(φ, sepIdentifier)
      Q(s1, h1, v1)})
  }

  private def produce3(s: State,
                       sf: (Sort, Verifier) => Term,
                       a: ast.Exp,
                       pve: PartialVerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Verifier) => VerificationResult)
                      : VerificationResult = {

    if (!a.isInstanceOf[ast.And]) {
      v.logger.debug(s"\nPRODUCE ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
      v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
    }

    val produced = a match {
      case ast.And(a0, a1) if !a.isPure || Verifier.config.handlePureConjunctsIndividually() =>
        val (sf0, sf1) = createSnapshotPair(s, sf, a0, a1, v)
        produce2(s, sf0, a0, pve, v)((s1, h1, v1) => {
          produce2(s1.copy(h = h1), sf1, a1, pve, v1)((s2, h2, v2) =>
            Q(s2, h2, v2))})

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
//        val impLog = new GlobalBranchRecord(imp, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]], "produce")
//        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
//        SymbExLogger.currentLog().initializeBranching()

        eval(s, e0, pve, v)((s1, t0, v1) => {
//          impLog.finish_cond()
          val branch_res = branch(s1, t0, v1,
            (s2, v2) => produce2(s2, sf, a0, pve, v2)((s3, h3, v3) => {
              val res1 = Q(s3, h3, v3)
//              impLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(impLog)
              res1}),
            (s2, v2) => {
              v2.decider.assume(sf(sorts.Snap, v2) === Unit)
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
              val res2 = Q(s2, s2.h, v2)
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
            (s2, v2) => produce2(s2, sf, a1, pve, v2)((s3, h3, v3) => {
              val res1 = Q(s3, h3, v3)
//              gbLog.finish_thnSubs()
//              SymbExLogger.currentLog().prepareOtherBranch(gbLog)
              res1}),
            (s2, v2) => produce2(s2, sf, a2, pve, v2)((s3, h3, v3) => {
              val res2 = Q(s3, h3, v3)
//              gbLog.finish_elsSubs()
              res2}))
//          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case let: ast.Let if !let.isPure => ???
//        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) =>
//          produce2(σ \+ γ1, sf, body, pve, c1)(Q))

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), perm) =>
        /* TODO: Verify similar to the code in DefaultExecutor/ast.NewStmt - unify */
        def addNewChunk(s: State, h: Heap, rcvr: Term, snap: Term, p: Term, v: Verifier)
                       (Q: (State, Heap, Verifier) => VerificationResult)
                       : VerificationResult = {

          if (s.qpFields.contains(field)) {
            ???
//            val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, rcvr, s)
//            optFvfDef.foreach(fvfDef => assume(fvfDef.valueDefinitions))
//            val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(rcvr, field.name, fvf, p)
//            val c1 = optFvfDef.fold(c)(fvfDef => c.copy(functionRecorder = c.functionRecorder.recordFvfAndDomain(fvfDef, Seq.empty)))
//            (h + ch, c1)
          } else {
            val ch = FieldChunk(rcvr, field.name, snap, p)
            chunkSupporter.produce(s, h, ch, v)(Q)
          }
        }

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assume(PermAtMost(NoPerm(), tPerm))
            v2.decider.assume(Implies(PermLess(NoPerm(), tPerm), tRcvr !== Null()))
            val snap = sf(v2.symbolConverter.toSort(field.typ), v2)
            val gain = PermTimes(tPerm, s2.permissionScalingFactor)
            addNewChunk(s2, s2.h, tRcvr, snap, gain, v2)(Q)}))

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), perm) =>
        val predicate = Verifier.program.findPredicate(predicateName)

        def addNewChunk(s: State, h: Heap, args: Seq[Term], snap: Term, p: Term, v: Verifier)
                       (Q: (State, Heap, Verifier) => VerificationResult)
                       : VerificationResult = {

          if (s.qpPredicates.contains(predicate)) {
            ???
//            decider.prover.comment("define formalVArgs")
//            val formalArgs:Seq[Var] = c.predicateFormalVarMap(predicate)
//            decider.prover.comment("createPredicateSnapFunction")
//            val (psf, optPsfDef) = quantifiedPredicateChunkSupporter.createPredicateSnapFunction(predicate, args, formalArgs, s, c)
//            decider.prover.comment("assume snapDefinition")
//            optPsfDef.foreach(psfDef => assume(psfDef.snapDefinitions))
//            val ch = quantifiedPredicateChunkSupporter.createSingletonQuantifiedPredicateChunk(args, formalArgs, predicate.name, psf, p)
//            (h + ch, c)
          } else {
            val snap1 = snap.convert(sorts.Snap)
            val ch = PredicateChunk(predicate.name, args, snap1, p)
            chunkSupporter.produce(s, h, ch, v)((s1, h1, v1) => {
              if (Verifier.config.enablePredicateTriggersOnInhale() && s1.functionRecorder == NoopFunctionRecorder)
              v1.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap1 +: args))
              Q(s1, h1, v1)
            })
          }
        }

        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, perm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assume(PermAtMost(NoPerm(), tPerm))
//            val snap = sf(s2.predicateSnapMap(predicate))
            val snap = sf(predicate.body.map(getOptimalSnapshotSort(_, Verifier.program, v2)._1).getOrElse(sorts.Snap), v2)
            val gain = PermTimes(tPerm, s2.permissionScalingFactor)
            addNewChunk(s2, s2.h, tArgs, snap, gain, v2)(Q)}))

      case wand: ast.MagicWand => ???
//        magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) =>
//          Q(σ.h + chWand, c1))

      case ast.utility.QuantifiedPermissions.QPForall(qvar, cond, rcvr, field, perm, forall, _) => ???
//        val qid = s"prog.l${utils.ast.sourceLine(forall)}"
//        evalQuantified(σ, Forall, Seq(qvar.localVar), Seq(cond), Seq(rcvr, perm), None, qid, pve, c){
//          case (Seq(tQVar), Seq(tCond), Seq(tRcvr, tPerm), _, Left(tAuxQuantNoTriggers), c1) =>
//            val snap = sf(sorts.FieldValueFunction(toSort(field.typ)))
//            val additionalInvFctArgs = c1.quantifiedVariables
//            val gain = PermTimes(tPerm, c1.permissionScalingFactor)
//            val (ch, invFct) = quantifiedChunkSupporter.createQuantifiedFieldChunk(tQVar, tRcvr, field, snap, gain, tCond, additionalInvFctArgs)
//
//            /* [2016-10-26 Malte]
//             * The issue described (and solved) in the previous comment is no longer a problem
//             * because quantifiers with FVFs in their triggers are rewritten by abstracting over
//             * the concrete FVF with a newly added, quantified variable. This allows the prover
//             * to instantiate the nesting axiom with any FVF and to get to the nested definitional
//             * axioms.
//             * The next comment is kept for documentary purposes.
//             *
//             * [2015-11-13 Malte]
//             * Using the trigger of the inv-of-receiver definitional axiom of the new inverse
//             * function as the trigger of the auxiliary quantifier seems like a good choice
//             * because whenever we need to learn something about the new inverse function,
//             * we might be interested in the auxiliary assumptions as well.
//             *
//             * This choice of triggers, however, might be problematic when quantified field
//             * dereference chains, e.g. x.g.f, where access to x.g and to x.g.f is quantified,
//             * are used in pure assertions, as witnessed by method test04 in test case
//             * quantified permissions/sets/generalised_shape.sil.
//             *
//             * In such a scenario, the receiver of (x.g).f will be an fvf-lookup, e.g.
//             * lookup_g(fvf1, x), but since fvf1 was introduced when evaluating x.g, the
//             * definitional axioms will be nested under the quantifier that is triggered by
//             * lookup_g(fvf1, x). In particular, the lookup definitional axiom, i.e. the one
//             * stating that lookup_g(fvf1, x) == lookup_g(fvf0, x) will be nested.
//             *
//             * Since we (currently) introduce a new FVF per field dereference, asserting that
//             * we have permissions to (x.g).f (e.g. at some later point) will introduce a new
//             * FVF fvf2, alongside a definitional axiom stating that
//             * lookup_g(fvf2, x) == lookup_g(fvf0, x).
//             *
//             * In order to prove that we hold permissions to (x.g).f, we would need to
//             * instantiate the auxiliary quantifier, but that quantifier is only triggered by
//             * lookup_g(fvf1, x).
//             *
//             * Hence, we do the following: if the only trigger for the auxiliary quantifier is
//             * of the shape lookup_g(fvf1, x), then we search the body for the equality
//             * lookup_g(fvf1, x) == lookup_g(fvf0, x), and we use lookup_g(fvf0, x) as the
//             * trigger. Searching the body is only necessary because, at the current point, we
//             * no longer know the relation between fvf1 and fvf0 (it could be preserved, though).
//             */
//            decider.prover.comment("Nested auxiliary terms")
//            assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars, /* The trigger generation code might have added quantified variables to invOfFct */
//                                            triggers = invFct.invOfFct.triggers))
//            val gainNonNeg = Forall(invFct.invOfFct.vars, perms.IsNonNegative(tPerm), invFct.invOfFct.triggers, s"$qid-perm")
//            assume(gainNonNeg)
//            decider.prover.comment("Definitional axioms for inverse functions")
//            assume(invFct.definitionalAxioms)
//            val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
//            val ch1 = ch.copy(hints = hints)
//            val tNonNullQuant = quantifiedChunkSupporter.receiverNonNullAxiom(tQVar, tCond, tRcvr, tPerm)
//            decider.prover.comment("Receivers are non-null")
//            assume(tNonNullQuant)
//            val c2 = c1.copy(functionRecorder = c1.functionRecorder.recordFieldInv(invFct))
//            Q(σ.h + ch1, c2)}

      case ast.utility.QuantifiedPermissions.QPPForall(qvar, cond, args, predname, gain, forall, _) => ???
//        //create new quantified predicate chunk
//        val predicate = c.program.findPredicate(predname)
//        val qid = s"prog.l${utils.ast.sourceLine(forall)}"
//        evalQuantified(σ, Forall, Seq(qvar.localVar), Seq(cond), args ++ Seq(gain) , None, qid, pve, c) {
//          case (Seq(tQVar), Seq(tCond), tArgsGain, _, Left(tAuxQuantNoTriggers), c1) =>
//            val (tArgs, Seq(tGain)) = tArgsGain.splitAt(args.size)
//            val snap = sf(sorts.PredicateSnapFunction(c.predicateSnapMap(predicate)))
//            val additionalInvFctArgs = c1.quantifiedVariables
//
//            val gain = PermTimes(tGain, c1.permissionScalingFactor)
//            val (ch, invFct) =
//              quantifiedPredicateChunkSupporter.createQuantifiedPredicateChunk(tQVar, predicate, c.predicateFormalVarMap(predicate), tArgs, snap, gain, tCond,
//                additionalInvFctArgs)
//
//            decider.prover.comment("Nested auxiliary terms")
//            assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars, /* The trigger generation code might have added quantified variables to invOfFct */
//              triggers = invFct.invOfFct.triggers))
//
//            val gainNonNeg = Forall(invFct.invOfFct.vars, perms.IsNonNegative(tGain), invFct.invOfFct.triggers, s"$qid-perm")
//            assume(gainNonNeg)
//            decider.prover.comment("Definitional axioms for inverse functions")
//            assume(invFct.definitionalAxioms)
//            val hints = quantifiedPredicateChunkSupporter.extractHints(Some(tQVar), Some(tCond), tArgs)
//            val ch1 = ch.copy(hints = hints)
//            val c2 = c1.copy(functionRecorder = c1.functionRecorder.recordPredInv(invFct))
//            Q(σ.h + ch1, c2)}

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit) /* TODO: See comment for case ast.Implies above */
        eval(s, a, pve, v)((s1, t, v1) => {
          v1.decider.assume(t)
          Q(s1, s1.h, v1)})
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
