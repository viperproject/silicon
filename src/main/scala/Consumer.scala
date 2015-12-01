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
import silver.verifier.reasons.{ReceiverNotInjective, InsufficientPermission, NegativePermission, AssertionFalse,
  ReceiverNull}
import interfaces.state.{StateFactory, Store, Heap, PathConditions, State, StateFormatter}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{QuantifiedChunk, SymbolConvert, DirectChunk, DefaultContext}
import state.terms._
import state.terms.predef.`?r`
import supporters.{LetHandler, Brancher, ChunkSupporter}
import supporters.qps.QuantifiedChunkSupporter

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
                      PC <: PathConditions[PC], S <: State[ST, H, S]]
    extends NoOpStatefulComponent
       with Consumer[DirectChunk, ST, H, S, DefaultContext]
    { this: Logging with Evaluator[ST, H, S, DefaultContext]
                    with Brancher[ST, H, S, DefaultContext]
                    with ChunkSupporter[ST, H, PC, S]
                    with LetHandler[ST, H, S, DefaultContext] =>

  private type C = DefaultContext

  protected val decider: Decider[ST, H, PC, S, C]
  import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val bookkeeper: Bookkeeper
  protected val config: Config

  private val qpForallCache = MMap[(ast.Forall, Set[QuantifiedChunk]), (Var, Term, Term, Seq[Term], H, QuantifiedChunk, C)]()

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
  def consume(σ: S, p: Term, φ: ast.Exp, pve: PartialVerificationError, c: C)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult =

    consume(σ, σ.h, p, φ.whenExhaling, pve, c)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))

  def consumes(σ: S,
               p: Term,
               φs: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), pvef, c)(Q)

  private def consumes(σ: S,
                       h: H,
                       p: Term,
                       φs: Seq[ast.Exp],
                       pvef: ast.Exp => PartialVerificationError,
                       c: C)
                       (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    /* Note: See the code comment about produce vs. produces in
     * DefaultProducer.produces. The same applies to consume vs. consumes.
     */

    if (φs.isEmpty)
      Q(σ \ h, Unit, Nil, c)
    else {
      val φ = φs.head

      if (φs.tail.isEmpty)
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          Q(σ \ h1, s1, dcs1, c1))
      else
        consume(σ, h, p, φ, pvef(φ), c)((h1, s1, dcs1, c1) =>
          consumes(σ, h1, p, φs.tail, pvef, c1)((h2, s2, dcs2, c2) => {
            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c2)}))
    }

  protected def consume(σ: S, h: H, p: Term, φ: ast.Exp, pve: PartialVerificationError, c: C)
                       (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      log.debug(s"\nCONSUME ${φ.pos}: $φ")
      log.debug(stateFormatter.format(σ))
      log.debug("h = " + stateFormatter.format(h))
    }

    val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure || config.handlePureConjunctsIndividually() =>
        consume(σ, h, p, a1, pve, c)((h1, s1, dcs1, c1) =>
          consume(σ, h1, p, a2, pve, c1)((h2, s2, dcs2, c2) => {
            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c2)}))

      case ast.Implies(e0, a0) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c,
            (c2: C) => consume(σ, h, p, a0, pve, c2)(Q),
            (c2: C) => Q(h, Unit, Nil, c2)))

      case ast.CondExp(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c,
            (c2: C) => consume(σ, h, p, a1, pve, c2)(Q),
            (c2: C) => consume(σ, h, p, a2, pve, c2)(Q)))

      case ast.QuantifiedPermissionSupporter.ForallRefPerm(qvar, condition, rcvr, field, loss, forall, fa) =>
        val tQVar = decider.fresh(qvar.name, toSort(qvar.typ))
        val γQVar = Γ(ast.LocalVar(qvar.name)(qvar.typ), tQVar)
        val σQVar = σ \+ γQVar
        val πPre = decider.π
        val c0 = c.copy(quantifiedVariables = tQVar +: c.quantifiedVariables)
        decider.locally[(Term, Term, Term, Iterable[Term], Quantification, C)](QB =>
          eval(σQVar, condition, pve, c0)((tCond, c1) =>
            if (decider.check(σQVar, Not(tCond), config.checkTimeout())) {
              /* The condition cannot be satisfied, hence we don't need to consume anything. */
              val c2 = c1.copy(quantifiedVariables = c1.quantifiedVariables.tail)
              Q(h, Unit, Nil, c2)
            } else {
              decider.assume(tCond)
              val c2 = c1.copy(branchConditions = tCond +: c1.branchConditions)
              eval(σQVar, rcvr, pve, c2)((tRcvr, c3) =>
                decider.assert(σ, tRcvr !== Null()) {
                  case true =>
                    eval(σQVar, loss, pve, c3)((pLoss, c4) =>
                      decider.assert(σ, perms.IsNonNegative(pLoss)) {
                        case true =>
                          /* TODO: Can we omit/simplify the injectivity check in certain situations? */
                          val receiverInjective = quantifiedChunkSupporter.injectivityAxiom(tQVar, tCond, tRcvr)
                          decider.assert(σ, receiverInjective) {
                            case true =>
                              val πDelta = decider.π -- πPre - tCond /* Removing tCond is crucial since it is not an auxiliary term */
                                val (tAuxTopLevel, tAuxNested) = state.utils.partitionAuxiliaryTerms(πDelta)
                              val tAuxQuantNoTriggers = Forall(tQVar, And(tAuxNested), Nil, s"prog.l${utils.ast.sourceLine(forall)}-aux")
                              val c5 = c4.copy(quantifiedVariables = c4.quantifiedVariables.tail,
                                               branchConditions = c4.branchConditions.tail)
                              QB(tCond, tRcvr, pLoss, tAuxTopLevel, tAuxQuantNoTriggers, c5)
                            case false =>
                              Failure[ST, H, S](pve dueTo ReceiverNotInjective(fa))}
                        case false =>
                          Failure[ST, H, S](pve dueTo NegativePermission(loss))})
                  case false =>
                    Failure[ST, H, S](pve dueTo ReceiverNull(fa))})})
        ){case (tCond, tRcvr, pLoss, tAuxTopLevel, tAuxQuantNoTriggers, c1) =>
            val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            val invFct =
              quantifiedChunkSupporter.getFreshInverseFunction(tQVar, tRcvr, tCond, c.snapshotRecorder.fold(Seq[Var]())(_.functionArgs))
            decider.prover.logComment("Top-level auxiliary terms")
            assume(tAuxTopLevel)
            decider.prover.logComment("Nested auxiliary terms")
            assume(tAuxQuantNoTriggers.copy(triggers = invFct.invOfFct.triggers)) /* NOTE: It might be necessary to do the same as in DefaultProducer */
  //          val (quantifiedChunks, _) = quantifiedChunkSupporter.splitHeap(h2, field.name)
  //          qpForallCache.get((forall, toSet(quantifiedChunks))) match {
                /* TODO: Re-enable caching. Needs to take context.branchConditions into account as well. Something else? */
  //            case Some((tQVarCached, tRcvrCached, tCondCached, invAxiomsCached, hCached, chCached, cCached))
  //              if tRcvr == tRcvrCached.replace(tQVarCached, tQVar) && tCond == tCondCached.replace(tQVarCached, tQVar) =>
  //              assume(invAxiomsCached)
  //              Q(hCached, chCached.fvf, /*ch :: */Nil, cCached)
  //            case _ =>
            decider.prover.logComment("Definitional axioms for inverse functions")
            assume(invFct.definitionalAxioms)
            val inverseReceiver = invFct(`?r`) // e⁻¹(r)
            quantifiedChunkSupporter.splitLocations(σ, h, field, Some(tQVar), inverseReceiver, tCond, tRcvr, PermTimes(pLoss, p), chunkOrderHeuristics, c1) {
              case Some((h1, ch, fvfDef, c2)) =>
                val fvfDomain = fvfDef.domainDefinitions(invFct)
                decider.prover.logComment("Definitional axioms for field value function")
                assume(fvfDomain ++ fvfDef.valueDefinitions)
//                if (!config.disableQPCaching())
//                  qpForallCache.update((forall, toSet(quantifiedChunks)), (tQVar, tRcvr, tCond, invFct.definitionalAxioms, h3, ch, c2))
                val c3 = c2.snapshotRecorder match {
                  case Some(sr) =>
                    val sr1 = sr.recordQPTerms(c2.quantifiedVariables,
                                               c2.branchConditions,
                                               invFct.definitionalAxioms ++ fvfDomain ++ fvfDef.valueDefinitions)
                    val sr2 =
                      if (true/*fvfDef.freshFvf*/) sr1.recordFvf(field, fvfDef.fvf)
                      else sr1
                    c2.copy(snapshotRecorder = Some(sr2))
                  case _ => c2}
                Q(h1, ch.fvf, /*ch :: */Nil, c3)
              case None =>
                Failure[ST, H, S](pve dueTo InsufficientPermission(fa))}
            //}
        }

      case ast.AccessPredicate(fa @ ast.FieldAccess(eRcvr, field), perm)
          if c.qpFields.contains(field) =>

        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          eval(σ, perm, pve, c1)((tPerm, c2) => {
            val condPerms = quantifiedChunkSupporter.singletonConditionalPermissions(tRcvr, tPerm)
            val hints = quantifiedChunkSupporter.extractHints(None, None, tRcvr)
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            quantifiedChunkSupporter.splitSingleLocation(σ, h, field, tRcvr, PermTimes(tPerm, p), chunkOrderHeuristics, c2) {
              case Some((h1, ch, fvfDef, c3)) =>
                assume(fvfDef.domainDefinitions ++ fvfDef.valueDefinitions)
                Q(h1, ch.valueAt(tRcvr), /*ch :: */ Nil, c3)
              case None => Failure[ST, H, S](pve dueTo InsufficientPermission(fa))
            }}))

      case let: ast.Let if !let.isPure =>
        handle[ast.Exp](σ, let, pve, c)((γ1, body, c1) =>
          consume(σ \+ γ1, h, p, body, pve, c1)(Q))

      case ast.AccessPredicate(locacc, perm) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          eval(σ, perm, pve, c1)((tPerm, c2) =>
            decider.assert(σ, perms.IsNonNegative(tPerm)){
              case true =>
                chunkSupporter.consume(σ, h, id, PermTimes(p, tPerm), pve, c2, locacc, Some(φ))(Q)
              case false =>
                Failure[ST, H, S](pve dueTo NegativePermission(perm))}))

      case _: ast.InhaleExhaleExp =>
        Failure[ST, H, S](utils.consistency.createUnexpectedInhaleExhaleExpressionError(φ))

      /* Any regular Expressions, i.e. boolean and arithmetic.
       * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
       * not in the partially consumed heap (h).
       */
      case _ =>
        decider.tryOrFail[(H, Term, List[DirectChunk])](σ, c)((σ1, c1, QS, QF) => {
          eval(σ1, φ, pve, c1)((t, c2) =>
            decider.assert(σ1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil), c2)
              case false =>
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(φ)))
            })
        })((res, c1) => Q(res._1, res._2, res._3, c1))
/* Consume pure expression w/o trying heuristics in case of failure */
/*
        eval(σ, φ, pve, c)((t, c) =>
          decider.assert(σ, t) {
            case true =>
              assume(t)
              Q(h, Unit, Nil, c)
            case false =>
              Failure[ST, H, S](pve dueTo AssertionFalse(φ))})
*/
    }

    consumed
  }

  /* Lifetime */

  override def reset() {
    super.reset()

    qpForallCache.clear()
  }
}
