/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.state.{Store, Heap, State, StateFormatter}
import viper.silicon.interfaces.{Failure, Producer, Consumer, Evaluator, VerificationResult}
import viper.silicon.interfaces.decider.Decider
import viper.silicon.reporting.Bookkeeper
import viper.silicon.state.{DefaultContext, FieldChunk, PredicateChunk, SymbolConvert, ListBackedHeap}
import viper.silicon.state.terms._
import viper.silicon.supporters._
import viper.silicon.supporters.qps.QuantifiedChunkSupporter
import viper.silicon.supporters.functions.NoopFunctionRecorder

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      S <: State[ST, H, S]]
    extends Producer[ST, H, S, DefaultContext[H]]
    { this: Logging with Evaluator[ST, H, S, DefaultContext[H]]
                    with Consumer[ST, H, S, DefaultContext[H]]
                    with Brancher[ST, H, S, DefaultContext[H]]
                    with MagicWandSupporter[ST, H, S]
                    with ChunkSupporterProvider[ST, H, S]
                    with LetHandler[ST, H, S, DefaultContext[H]] =>

  private type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, C]
  import decider.{fresh, assume}

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, S, C]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val bookkeeper: Bookkeeper
  protected val config: Config

  def produce(σ: S,
              sf: Sort => Term,
              p: Term,
              φ: ast.Exp,
              pve: PartialVerificationError,
              c: C)
             (Q: (S, C) => VerificationResult)
             : VerificationResult =

    produce2(σ, sf, p, φ.whenInhaling, pve, c)((h, c1) =>
      Q(σ \ h, c1))

  def produces(σ: S,
               sf: Sort => Term,
               p: Term,
               φs: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               c: C)
              (Q: (S, C) => VerificationResult)
              : VerificationResult = {

    /* Note: Produces(φs) allows more fine-grained error reporting when compared
     * to produce(BigAnd(φs)) because with produces, each φ in φs can be
     * produced with its own PartialVerificationError. The two differ in
     * behaviour, though, because producing a list of, e.g., preconditions, with
     * produce results in more explicit conjunctions, and thus in more
     * combine-terms, which can affect the snapshot structure of predicates and
     * functions.
     */

    if (φs.isEmpty)
      Q(σ, c)
    else {
      val φ = φs.head.whenInhaling

      if (φs.tail.isEmpty)
        produce(σ, sf, p, φ, pvef(φ), c)(Q)
      else {
        val (sf0, sf1) = createSnapshotPair(sf, φ, utils.ast.BigAnd(φs.tail), c)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter φs) is BigAnd-ed
           *       over and over again.
           */

        produce(σ, sf0, p, φ, pvef(φ), c)((σ1, c1) => {
          produces(σ1, sf1, p, φs.tail, pvef, c1)(Q)})
      }
    }
  }

  /** Wrapper Method for produce, for logging. See Executor.scala for explanation of analogue. **/
  private def produce2(σ: S,
                       sf: Sort => Term,
                       p: Term,
                       φ: ast.Exp,
                       pve: PartialVerificationError,
                       c: C)
                      (Q: (H, C) => VerificationResult)
                      : VerificationResult = {
    val sepIdentifier = SymbExLogger.currentLog().insert(new ProduceRecord(φ, σ, decider.pcs, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    produce3(σ, sf, p, φ, pve, c)((σ1, c1) => {
      SymbExLogger.currentLog().collapse(φ, sepIdentifier)
      Q(σ1, c1)})
  }

  private def produce3(σ: S,
                       sf: Sort => Term,
                       p: Term,
                       φ: ast.Exp,
                       pve: PartialVerificationError,
                       c: C)
                      (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      log.debug(s"\nPRODUCE ${utils.ast.sourceLineColumn(φ)}: $φ")
      log.debug(stateFormatter.format(σ, decider.π))
    }

    val produced = φ match {
      case ast.And(a0, a1) if !φ.isPure || config.handlePureConjunctsIndividually() =>
        val (sf0, sf1) = createSnapshotPair(sf, a0, a1, c)
        produce2(σ, sf0, p, a0, pve, c)((h1, c1) => {
          produce2(σ \ h1, sf1, p, a1, pve, c1)((h2, c2) =>
            Q(h2, c2))})

      case imp @ ast.Implies(e0, a0) if !φ.isPure =>
        val impLog = new GlobalBranchRecord(imp, σ, decider.pcs, c.asInstanceOf[DefaultContext[ListBackedHeap]], "produce")
        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
        SymbExLogger.currentLog().initializeBranching()

        eval(σ, e0, pve, c)((t0, c1) => {
          impLog.finish_cond()
          val branch_res = branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a0, pve, c2)((h_a1, c_a1) => {
              val res1 = Q(h_a1, c_a1)
              impLog.finish_thnSubs()
              SymbExLogger.currentLog().prepareOtherBranch(impLog)
              res1}),
            (c2: C) => {
              assume(sf(sorts.Snap) === Unit)
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
              val res2 = Q(σ.h, c2)
              impLog.finish_elsSubs()
              res2})
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ite @ ast.CondExp(e0, a1, a2) if !φ.isPure =>
        val gbLog = new GlobalBranchRecord(ite, σ, decider.pcs, c.asInstanceOf[DefaultContext[ListBackedHeap]], "produce")
        val sepIdentifier = SymbExLogger.currentLog().insert(gbLog)
        SymbExLogger.currentLog().initializeBranching()
        eval(σ, e0, pve, c)((t0, c1) => {
          gbLog.finish_cond()
          val branch_res = branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a1, pve, c2)((h_a1, c_a1) => {
              val res1 = Q(h_a1, c_a1)
              gbLog.finish_thnSubs()
              SymbExLogger.currentLog().prepareOtherBranch(gbLog)
              res1}),
            (c2: C) => produce2(σ, sf, p, a2, pve, c2)((h_a2, c_a2) => {
              val res2 = Q(h_a2, c_a2)
              gbLog.finish_elsSubs()
              res2}))
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case let: ast.Let if !let.isPure =>
        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) =>
          produce2(σ \+ γ1, sf, p, body, pve, c1)(Q))

      case acc @ ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        /* TODO: Verify similar to the code in DefaultExecutor/ast.NewStmt - unify */
        def addNewChunk(h: H, rcvr: Term, s: Term, p: Term, c: C): (H, C) =
          if (c.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, rcvr, s)
            optFvfDef.foreach(fvfDef => assume(fvfDef.valueDefinitions))
            val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(rcvr, field.name, fvf, p)
            (h + ch, c)
          } else {
            val ch = FieldChunk(rcvr, field.name, s, p)
            val (h1, c1) = chunkSupporter.produce(σ, h, ch, c)
            (h1, c1)
          }

        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          eval(σ, gain, pve, c1)((pGain, c2) => {
            assume(PermAtMost(NoPerm(), pGain))
            assume(Implies(PermLess(NoPerm(), pGain), tRcvr !== Null()))
            val s = sf(toSort(field.typ))
            val pNettoGain = PermTimes(pGain, p)
            val (h1, c3) = addNewChunk(σ.h, tRcvr, s, pNettoGain, c2)
            Q(h1, c3)}))

      case acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), gain) =>
        val predicate = c.program.findPredicate(predicateName)
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
          eval(σ, gain, pve, c1)((pGain, c2) => {
            assume(PermAtMost(NoPerm(), pGain))
            val s = sf(predicate.body.map(getOptimalSnapshotSort(_, c.program)._1).getOrElse(sorts.Snap))
            val pNettoGain = PermTimes(pGain, p)
            val ch = PredicateChunk(predicate.name, tArgs, s.convert(sorts.Snap), pNettoGain)
            val (h1, c3) = chunkSupporter.produce(σ, σ.h, ch, c2)
            Q(h1, c3)}))

      case wand: ast.MagicWand =>
        magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) =>
          Q(σ.h + chWand, c))

      case ast.utility.QuantifiedPermissions.QPForall(qvar, cond, rcvr, field, gain, forall, _) =>
        val qid = s"prog.l${utils.ast.sourceLine(forall)}"
        evalQuantified(σ, Forall, Seq(qvar.localVar), Seq(cond), Seq(rcvr, gain), Nil, qid, pve, c){
          case (Seq(tQVar), Seq(tCond), Seq(tRcvr, tGain), _, tAuxQuantNoTriggers, c1) =>
            val snap = sf(sorts.FieldValueFunction(toSort(field.typ)))
            val additionalInvFctArgs = c1.quantifiedVariables
            val (ch, invFct) =
              quantifiedChunkSupporter.createQuantifiedChunk(tQVar, tRcvr, field, snap, PermTimes(tGain, p), tCond,
                                                             additionalInvFctArgs)

            /* [2016-05-05 Malte]
             * The issue described (and solved) in the previous comment is no longer a problem
             * because FVF definitional axioms are no longer nested under other quantifiers.
             * The comment is kept for documentary purposes.
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
            decider.prover.logComment("Nested auxiliary terms")
            assume(tAuxQuantNoTriggers.copy(vars = invFct.invOfFct.vars, /* The trigger generation code might have added quantified variables to invOfFct */
                                            triggers = invFct.invOfFct.triggers))
            val gainNonNeg = Forall(invFct.invOfFct.vars, perms.IsNonNegative(tGain), invFct.invOfFct.triggers, s"$qid-perm")
            assume(gainNonNeg)
            decider.prover.logComment("Definitional axioms for inverse functions")
            assume(invFct.definitionalAxioms)
            val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
            val ch1 = ch.copy(hints = hints)
            val tNonNullQuant = quantifiedChunkSupporter.receiverNonNullAxiom(tQVar, tCond, tRcvr, PermTimes(tGain, p))
            decider.prover.logComment("Receivers are non-null")
            assume(Set(tNonNullQuant))
  //          decider.prover.logComment("Definitional axioms for field value functions")
  //          val c2 = c1.copy(functionRecorder = c1.functionRecorder.recordQPTerms(Nil, c1.branchConditions, invFct.definitionalAxioms))
            val c2 = c1.copy(functionRecorder = c1.functionRecorder.recordQPTerms(Nil, decider.pcs.branchConditions, invFct.definitionalAxioms))
            Q(σ.h + ch1, c2)}

      case _: ast.InhaleExhaleExp =>
        Failure(utils.consistency.createUnexpectedInhaleExhaleExpressionError(φ))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        assume(sf(sorts.Snap) === Unit) /* TODO: See comment for case ast.Implies above */
        eval(σ, φ, pve, c)((t, c1) => {
          assume(t)
          Q(σ.h, c1)})
    }

    produced
  }

  private def getOptimalSnapshotSort(φ: ast.Exp, program: ast.Program, visited: Seq[String] = Nil)
                                    : (Sort, Boolean) =

    φ match {
      case _ if φ.isPure =>
        (sorts.Snap, true)

      case ast.AccessPredicate(locacc, _) => locacc match {
        case fa: ast.FieldAccess =>
          (toSort(fa.field.typ), false)

        case pa: ast.PredicateAccess =>
          if (!visited.contains(pa.predicateName)) {
            program.findPredicate(pa.predicateName).body match {
              case None => (sorts.Snap, false)
              case Some(body) => getOptimalSnapshotSort(body, program, pa.predicateName +: visited)
            }
          } else
          /* We detected a cycle in the predicate definition and thus stop
           * inspecting the predicate bodies.
           */
            (sorts.Snap, false)
      }

      case ast.Implies(e0, φ1) =>
        /* φ1 must be impure, otherwise the first case would have applied. */
        getOptimalSnapshotSort(φ1, program, visited)

      case ast.And(φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */
        getOptimalSnapshotSortFromPair(φ1, φ2, () => (sorts.Snap, false), program, visited)

      case ast.CondExp(_, φ1, φ2) =>
        /* At least one of φ1, φ2 must be impure, otherwise ... */

        def findCommonSort() = {
          val (s1, isPure1) = getOptimalSnapshotSort(φ1, program, visited)
          val (s2, isPure2) = getOptimalSnapshotSort(φ2, program, visited)
          val s = if (s1 == s2) s1 else sorts.Snap
          val isPure = isPure1 && isPure2
          assert(!isPure)
          (s, isPure)
        }

        getOptimalSnapshotSortFromPair(φ1, φ2, findCommonSort, program, visited)

      case ast.utility.QuantifiedPermissions.QPForall(_, _, _, field, _, _, _) =>
      (sorts.FieldValueFunction(toSort(field.typ)), false)

      case _ =>
        (sorts.Snap, false)
    }

  private def getOptimalSnapshotSortFromPair(φ1: ast.Exp,
                                             φ2: ast.Exp,
                                             fIfBothPure: () => (Sort, Boolean),
                                             program: ast.Program,
                                             visited: Seq[String])
                                            : (Sort, Boolean) = {

    if (φ1.isPure && φ2.isPure) fIfBothPure()
    else (sorts.Snap, false)
  }

  private def mkSnap(φ: ast.Exp, program: ast.Program, visited: Seq[String] = Nil): Term =
    getOptimalSnapshotSort(φ, program, visited) match {
      case (sorts.Snap, true) => Unit
      case (sort, _) => fresh(sort)
    }

  @inline
  private def createSnapshotPair(sf: Sort => Term, a0: ast.Exp, a1: ast.Exp, c: C)
                                : (Sort => Term, Sort => Term) = {

    val (s0, s1) = createSnapshotPair(sf(sorts.Snap), a0, a1, c)

    val sf0 = (sort: Sort) => s0.convert(sort)
    val sf1 = (sort: Sort) => s1.convert(sort)

    (sf0, sf1)
  }

  private def createSnapshotPair(s: Term, a0: ast.Exp, a1: ast.Exp, c: C): (Term, Term) = {
    /* [2015-11-17 Malte] If both fresh snapshot terms and first/second datatypes
     * are used, then the overall test suite verifies in 2min 10sec, whereas
     * it takes 2min 20sec when only first/second datatypes are used. Might be
     * worth re-benchmarking from time to time.
     */

    if (c.functionRecorder == NoopFunctionRecorder) {
      val s0 = mkSnap(a0, c.program)
      val s1 = mkSnap(a1, c.program)

      val snapshotEq = (s, s0, s1) match {
        case (Unit, Unit, Unit) => True()
        case (Unit, _, _) => sys.error(s"Unexpected equality between $s and ($s0, $s1)")
        case _ => s === Combine(s0, s1)
      }

      assume(snapshotEq)

      (s0, s1)
    } else {
      val _s0 = First(s)
      val _s1 = Second(s)

      (_s0, _s1)
    }
  }
}
