/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import org.slf4s.Logging
import silver.ast
import silver.verifier.PartialVerificationError
import interfaces.state.{StateFactory, Store, Heap, PathConditions, State, StateFormatter}
import interfaces.{Failure, Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{DefaultContext, DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import state.terms._
import supporters.{LetHandler, Brancher, ChunkSupporter, QuantifiedChunkSupporter}
import viper.silver.ast.QuantifiedPermissionSupporter

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    extends Producer[ST, H, S, DefaultContext]
    { this: Logging with Evaluator[ST, H, S, DefaultContext]
                    with Consumer[DirectChunk, ST, H, S, DefaultContext]
                    with Brancher[ST, H, S, DefaultContext]
                    with ChunkSupporter[ST, H, PC, S]
                    with LetHandler[ST, H, S, DefaultContext] =>

  private type C = DefaultContext

  protected val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, assume}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S]
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

  private def produce2(σ: S,
                       sf: Sort => Term,
                       p: Term,
                       φ: ast.Exp,
                       pve: PartialVerificationError,
                       c: C)
                      (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      log.debug(s"\nPRODUCE ${φ.pos}: $φ")
      log.debug(stateFormatter.format(σ))
    }

    val produced = φ match {
      case ast.And(a0, a1) if !φ.isPure || config.handlePureConjunctsIndividually() =>
        val (sf0, sf1) = createSnapshotPair(sf, a0, a1, c)
        produce2(σ, sf0, p, a0, pve, c)((h1, c1) => {
          produce2(σ \ h1, sf1, p, a1, pve, c1)((h2, c2) =>
            Q(h2, c2))})

      case ast.Implies(e0, a0) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a0, pve, c2)(Q),
            (c2: C) => Q(σ.h, c2)))

      case ast.CondExp(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a1, pve, c2)(Q),
            (c2: C) => produce2(σ, sf, p, a2, pve, c2)(Q)))

      case let: ast.Let if !let.isPure =>
        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) =>
          produce2(σ \+ γ1, sf, p, body, pve, c1)(Q))

      case acc @ ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        /* TODO: Verify similar to the code in DefaultExecutor/ast.NewStmt - unify */
        def addNewChunk(h: H, rcvr: Term, s: Term, p: Term, c: C): (H, C) =
          if (c.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, rcvr, s)
            optFvfDef.foreach(fvfDef => assume(fvfDef.domainDefinition :: fvfDef.valueDefinition :: Nil))
            val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(rcvr, field.name, fvf, p)
            (h + ch, c)
          } else {
            val ch = DirectFieldChunk(rcvr, field.name, s, p)
            val (h1, c1) = chunkSupporter.produce(σ, h, ch, c)
            (h1, c1)
          }

        eval(σ, eRcvr, pve, c)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          eval(σ, gain, pve, c1)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = PermTimes(pGain, p)
            val (h1, c3) = addNewChunk(σ.h, tRcvr, s, pNettoGain, c2)
            Q(h1, c3)})})

      case acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), gain) =>
        val predicate = c.program.findPredicate(predicateName)
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
          eval(σ, gain, pve, c1)((pGain, c2) => {
            val s = sf(predicate.body.map(getOptimalSnapshotSort(_, c.program)._1).getOrElse(sorts.Snap))
            val pNettoGain = PermTimes(pGain, p)
            val ch = DirectPredicateChunk(predicate.name, tArgs, s.convert(sorts.Snap), pNettoGain)
            val (h1, c3) = chunkSupporter.produce(σ, σ.h, ch, c2)
            Q(h1, c3)}))

      case QuantifiedPermissionSupporter.ForallRefPerm(qvar, cond, rcvr, field, gain, forall, _) =>
        val tQVar = decider.fresh(qvar.name, toSort(qvar.typ))
        val γQVar = Γ(ast.LocalVar(qvar.name)(qvar.typ), tQVar)
        val σQVar = σ \+ γQVar
        val πPre = decider.π
        val c0 = c.copy(quantifiedVariables = tQVar +: c.quantifiedVariables)
        decider.locally[(Term, Term, Term, Iterable[Term], Quantification, C)](QB =>
          eval(σQVar, cond, pve, c0)((tCond, c1) => {
            assume(tCond)
            val c1a = c1.copy(branchConditions = tCond +: c1.branchConditions)
            eval(σQVar, rcvr, pve, c1a)((tRcvr, c2) =>
              eval(σQVar, gain, pve, c2)((pGain, c3) => {
                val πDelta = decider.π -- πPre - tCond /* Removing tCond is crucial since it is not an auxiliary term */
                val (tAuxTopLevel, tAuxNested) = state.utils.partitionAuxiliaryTerms(πDelta)
                val tAuxQuantNoTriggers = Forall(tQVar, And(tAuxNested), Nil, s"prog.l${utils.ast.sourceLine(forall)}-aux")
                val c4 = c3.copy(quantifiedVariables = c.quantifiedVariables,
                                 branchConditions = c.branchConditions)
                QB(tCond, tRcvr, pGain, tAuxTopLevel, tAuxQuantNoTriggers, c4)}))})
        ){case (tCond, tRcvr, pGain, tAuxTopLevel, tAuxQuantNoTriggers, c1) =>
          val snap = sf(sorts.FieldValueFunction(toSort(field.typ)))
          val additionalInvFctArgs = c.snapshotRecorder.fold(Seq[Var]())(_.functionArgs)
          val (ch, invFct) =
            quantifiedChunkSupporter.createQuantifiedChunk(tQVar, tRcvr, field, snap, PermTimes(pGain, p), tCond,
                                                           additionalInvFctArgs)
          decider.prover.logComment("Top-level auxiliary terms")
          assume(tAuxTopLevel)

          /* [2015-11-13 Malte]
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
           * lookup_g(fvf1, x) == lookup_g(fvf0, x), and we add as another trigger.
           * Searching the body is only necessary because, at the current point, we no longer
           * no the relation between fvf1 and fvf0 (it could be preserved, though).
           */
          val triggerForAuxQuant = invFct.invOfFct.triggers match {
            case Seq(trigger @ Trigger(Seq(lk: Lookup))) => /* TODO: Make more specific */
              /* We need to look for the equality lookup_g(fvf1, ?r) == lookup_g(fvf0, ?r) */
              var optSourceLkR: Option[Lookup] = None
              val lkR = lk.copy(at = predef.`?r`)
              tAuxQuantNoTriggers.visit { case BuiltinEquals(`lkR`, sourceLkR: Lookup) => optSourceLkR = Some(sourceLkR) }
              /* Trigger {lookup_g(fvf1, x), lookup_g(fvf0, x)} */
              Seq(optSourceLkR.fold(trigger)(sourceLkR => Trigger(sourceLkR.copy(at = lk.at) :: Nil)))
            case other =>
              /* Trigger {lookup_g(fvf1, x)} */
              other
          }
          decider.prover.logComment("Nested auxiliary terms")
          assume(tAuxQuantNoTriggers.copy(triggers = triggerForAuxQuant))
          decider.prover.logComment("Definitional axioms for inverse functions")
          assume(invFct.definitionalAxioms)
          val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
          val ch1 = ch.copy(hints = hints)
          val tNonNullQuant = quantifiedChunkSupporter.receiverNonNullAxiom(tQVar, tCond, tRcvr, PermTimes(pGain, p))
          decider.prover.logComment("Receivers are non-null")
          assume(Set(tNonNullQuant))
          decider.prover.logComment("Definitional axioms for field value functions")
          val c2 = c1.snapshotRecorder match {
            case Some(sr) =>
              val sr1 = sr.recordQPTerms(Nil, c1.branchConditions, invFct.definitionalAxioms)
              c1.copy(snapshotRecorder = Some(sr1))
            case None =>
              c1}
          Q(σ.h + ch1, c2)}

      case _: ast.InhaleExhaleExp =>
        Failure[ST, H, S](utils.consistency.createUnexpectedInhaleExhaleExpressionError(φ))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
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

      case ast.Forall(_, _, ast.Implies(_, ast.FieldAccessPredicate(ast.FieldAccess(_, f), _))) =>
      (sorts.FieldValueFunction(toSort(f.typ)), false)

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

    if (c.snapshotRecorder.isEmpty) {
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
