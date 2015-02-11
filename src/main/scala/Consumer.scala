/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.ast
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{ReceiverNotInjective, InsufficientPermission, NegativePermission, AssertionFalse}
import interfaces.state.{StateFactory, Store, Heap, PathConditions, State, StateFormatter}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{SymbolConvert, DirectChunk, DefaultContext}
import state.terms._
import state.terms.predef.`?r`
import supporters.{LetHandler, Brancher, ChunkSupporter, QuantifiedChunkSupporter}

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
                      PC <: PathConditions[PC], S <: State[ST, H, S]]
    extends Consumer[DirectChunk, ST, H, S, DefaultContext]
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

      if (φ.tail.isEmpty)
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
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
    }

    val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure =>
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

      case QuantifiedChunkSupporter.ForallRef(qvar, condition, rcvr, field, loss, forall, fa) =>
        val tQVar = decider.fresh(qvar.name, toSort(qvar.typ))
        val γQVar = Γ(ast.LocalVar(qvar.name)(qvar.typ), tQVar)
        val (h1, ts) = quantifiedChunkSupporter.quantifyHeapForFields(σ.h, QuantifiedChunkSupporter.fieldAccesses(forall))
          /* If receiver or condition dereference a field which hasn't been quantified yet,
           * then the evaluator will try to find a regular chunk for the quantified variable,
           * which will fail.
           * TODO: It would be better if the heap were quantified on-demand (e.g., in the
           *       evaluator) AND if that quantified heap would be used afterwards as well
           *       (which would currently not be possible since the evaluator cannot pass
           *       on modified heaps).
           */
        assume(ts)
        val σQVar = σ \ h1 \+ γQVar
        val c0 = c.copy(quantifiedVariables = tQVar +: c.quantifiedVariables)
        eval(σQVar, condition, pve, c0)((tCond, c1) =>
          if (decider.check(σQVar, Not(tCond))) {
            /* The condition cannot be satisfied, hence we don't need to consume anything. */
            val c2 = c1.copy(quantifiedVariables = c1.quantifiedVariables.tail)
            Q(h, Unit, Nil, c2)
          } else {
            decider.assume(tCond)
            eval(σQVar, loss, pve, c1)((tPerm, c2) =>
              decider.assert(σ, perms.IsNonNegative(tPerm)) {
                case true =>
                  eval(σQVar, rcvr, pve, c2)((tRcvr, c3) => {
                    val receiverInjective =
                      if (!decider.check(σQVar, PermLess(FullPerm(), PermPlus(tPerm, tPerm)))) {
                        quantifiedChunkSupporter.injectivityAxiom(tQVar, tCond, tRcvr)
                      } else
                        True()
                    decider.assert(σ, receiverInjective) {
                      case true =>
                        val c3a = c3.copy(quantifiedVariables = c3.quantifiedVariables.tail)
                        val (h2, ts) = quantifiedChunkSupporter.quantifyChunksForField(h, field)
                        val (inverseRcvrFunc, inverseRcvrFuncAxioms) =
                          quantifiedChunkSupporter.getFreshInverseFunction(tRcvr, tCond, tQVar)
                        val quantifiedInverseRcvr = inverseRcvrFunc(`?r`)
                        val condPerms = quantifiedChunkSupporter.conditionalPermissions(tQVar, quantifiedInverseRcvr, tCond, tPerm)
                        assume(ts ++ inverseRcvrFuncAxioms)
                        val hints = quantifiedChunkSupporter.extractHints(Some(tQVar), Some(tCond), tRcvr)
                        val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                        val tRcvrUsingInv = tRcvr.replace(tQVar, quantifiedInverseRcvr)
                        quantifiedChunkSupporter.splitLocations(σ, h2, field, tRcvr, tQVar, tRcvrUsingInv, PermTimes(tPerm, p), PermTimes(condPerms, p), chunkOrderHeuristics, c3a) {
                          case Some((h3, ch, c4)) =>
                            Q(h3, ch.value, /*ch :: */Nil, c4)
                          case None =>
                            Failure[ST, H, S](pve dueTo InsufficientPermission(fa))}

                      case false =>
                        Failure[ST, H, S](pve dueTo ReceiverNotInjective(fa))}})

                case false =>
                  Failure[ST, H, S](pve dueTo NegativePermission(loss))})})

      case ast.AccessPredicate(fa @ ast.FieldAccess(eRcvr, field), perm)
          if quantifiedChunkSupporter.isQuantifiedFor(h, field.name) =>

        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          eval(σ, perm, pve, c1)((tPerm, c2) => {
            val condPerms = quantifiedChunkSupporter.singletonConditionalPermissions(tRcvr, tPerm)
            val hints = quantifiedChunkSupporter.extractHints(None, None, tRcvr)
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            // TODO: What to pass as receiverUsingInverseFunction to splitSingleLocation?
            quantifiedChunkSupporter.splitSingleLocation(σ, h, field, tRcvr, tRcvr, PermTimes(tPerm, p), PermTimes(condPerms, p), chunkOrderHeuristics, c2) {
              case Some((h1, ch, c3)) =>
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
        decider.tryOrFail[(H, Term, List[DirectChunk], C)](σ, c)((σ1, QS, QF) => {
          eval(σ1, φ, pve, c)((t, c) =>
            decider.assert(σ1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c))
              case false =>
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(φ)))
            })
        })(Q.tupled)
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
}
