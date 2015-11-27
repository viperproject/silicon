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
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter}
import interfaces.{Failure, Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{DefaultContext, DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import state.terms._
import supporters.{LetHandler, Brancher, ChunkSupporter}

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

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

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
            (c2: C) => {
              assume(sf(sorts.Snap) === Unit)
                /* TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                 * otherwise. In order words, only make this assumption if `sf` has
                 * already been used, e.g. in a snapshot equality such as `s0 == (s1, s2)`.
                 */
              Q(σ.h, c2)}))

      case ast.CondExp(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c1,
            (c2: C) => produce2(σ, sf, p, a1, pve, c2)(Q),
            (c2: C) => produce2(σ, sf, p, a2, pve, c2)(Q)))

      case let: ast.Let if !let.isPure =>
        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) =>
          produce2(σ \+ γ1, sf, p, body, pve, c1)(Q))

      case acc @ ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          eval(σ, gain, pve, c1)((pGain, c2) => {
            assume(PermAtMost(NoPerm(), pGain))
            val s = sf(toSort(field.typ))
            val pNettoGain = PermTimes(pGain, p)
            val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
            val (h1, c3) = chunkSupporter.produce(σ, σ.h, ch, c2)
            Q(h1, c3)})})

      case acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), gain) =>
        val predicate = c.program.findPredicate(predicateName)
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
          eval(σ, gain, pve, c1)((pGain, c2) => {
            assume(PermAtMost(NoPerm(), pGain))
            val s = sf(predicate.body.map(getOptimalSnapshotSort(_, c.program)._1).getOrElse(sorts.Snap))
            val pNettoGain = PermTimes(pGain, p)
            val ch = DirectPredicateChunk(predicate.name, tArgs, s.convert(sorts.Snap), pNettoGain)
            val (h1, c3) = chunkSupporter.produce(σ, σ.h, ch, c2)
            Q(h1, c3)}))

      case _: ast.InhaleExhaleExp =>
        Failure[ST, H, S](utils.consistency.createUnexpectedInhaleExhaleExpressionError(φ))

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

      case ast.Forall(_, _, ast.Implies(_, ast.FieldAccessPredicate(ast.FieldAccess(_, f), _))) =>
        (toSort(f.typ), false)

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
