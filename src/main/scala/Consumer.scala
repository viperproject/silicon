/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.PartialVerificationError
import silver.verifier.reasons.{InsufficientPermission, NonPositivePermission, AssertionFalse}
import interfaces.state.{StateFactory, Store, Heap, PathConditions, State, StateFormatter, ChunkIdentifier}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{SymbolConvert, DirectChunk, DirectFieldChunk, DirectPredicateChunk, DefaultContext}
import state.terms._
import state.terms.perms.{IsPositive, IsNoAccess}
import heap.QuantifiedChunkHelper

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S]]
		extends Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext]
									  with Brancher[ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult =

    consume(σ, σ.h, p, φ.whenExhaling, pve, c)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))

  def consumes(σ: S,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), pvef, c)(Q)

  private def consumes(σ: S,
                       h: H,
                       p: P,
                       φs: Seq[ast.Expression],
                       pvef: ast.Expression => PartialVerificationError,
                       c: C)
                       (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    /* TODO: See the code comment about produce vs. produces in DefaultProducer.produces.
     *       The same applies to consume vs. consumes.
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
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)
          }))
    }

  protected def consume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C)
			                 (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {

    internalConsume(σ, h, p, φ, pve, c)((h1, s1, dcs, c1) => {
      Q(h1, s1, dcs, c1)
    })
  }

  private def internalConsume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C)
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
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = c1.snapshotRecorder.get
                val sr2 = c2.snapshotRecorder.get
                val snap1 = if (s1 == Unit) Unit else sr1.currentSnap
                val snap2 = if (s2 == Unit) Unit else sr2.currentSnap
                c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = Combine(snap1, snap2))))
              case _ => c2}

						Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c3)}))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c)((t0, c1) =>
					branch(σ, t0, c,
						(c2: C) => consume(σ, h, p, a0, pve, c2)(Q),
						(c2: C) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branch(σ, t0, c,
            (c2: C) => consume(σ, h, p, a1, pve, c2)(Q),
            (c2: C) => consume(σ, h, p, a2, pve, c2)(Q)))

      case QuantifiedChunkHelper.QuantifiedSetAccess(qvar, condition, rcvr, field, loss, fa) =>
        println(s"\n[Consumer/QuantifiedSetAccess] $φ")
        val tQVar = decider.fresh(qvar.name, toSort(qvar.typ))
        println(s"  tQVar = $tQVar")
        val γQVar = Γ(ast.LocalVariable(qvar.name)(qvar.typ), tQVar)
        val (h1, ts) = quantifiedChunkHelper.quantifyHeapForMentionedFields(σ.h, rcvr :: condition :: Nil)
          /* If receiver or condition dereference a field which hasn't been quantified yet,
           * then the evaluator will try to find a regular chunk for the quantified variable,
           * which will fail.
           * TODO: It would be better if the heap were quantified on-demand (e.g., in the
           *       evaluator) AND if that quantified heap would be used afterwards as well
           *       (which would currently not be possible since the evaluator cannot pass
           *       on modified heaps).
           */
//          if (quantifiedChunkHelper.isQuantifiedFor(h, field.name)) (h, Set.empty[Term])
//          else quantifiedChunkHelper.quantifyChunksForField(h, field)
        assume(ts)
        val σQVar = σ \ h1 \+ γQVar
        eval(σQVar, condition, pve, c)((tCond, c1) => {
          println(s"  tCond = $tCond")
          if (decider.check(σQVar, Not(tCond)))
            /* The condition cannot be satisfied, hence we don't need to consume anything. */
            Q(h, Unit, Nil, c1)
          else {
            decider.assume(tCond)

this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars = tQVar +: this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars

            eval(σQVar, rcvr, pve, c1)((tRcvr, c1a) => {
              println(s"\n  tRcvr = $tRcvr")
              evalp(σQVar, loss, pve, c1a)((tPerm, c2) => {

this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars = this.asInstanceOf[DefaultEvaluator[ST, H, PC, C]].quantifiedVars.drop(1)

                decider.assert(σ, IsPositive(tPerm)) {
                  case true =>
                    val (h2, ts) = quantifiedChunkHelper.quantifyChunksForField(h, field)
//                      if (quantifiedChunkHelper.isQuantifiedFor(h, field.name)) (h, Set.empty[Term])
//                      else quantifiedChunkHelper.quantifyChunksForField(h, field)
                    assume(ts)
                    val arbitraryInverseRcvr = quantifiedChunkHelper.getInverseFunction(tRcvr)(`?r`)
                    val condPerms = quantifiedChunkHelper.conditionalPermissions(tQVar, arbitraryInverseRcvr, tCond, tPerm)
                    println(s"  h2 = $h2")
                    println(s"  tPerm = $tPerm")
                    println(s"  arbitraryInverseRcvr = $arbitraryInverseRcvr")
                    println(s"  condPerms = $condPerms")
                    /* TODO: In cases where the receiver is just the quantified variable, i.e., where
                     *       explicitly and implicitly quantified receiver coincide, we can save a
                     *       fresh term by passing in tQVar such that it can be used instead of a
                     *       fresh skolem variable.
                     */
//                    quantifiedChunkHelper.splitLocations(σ, h2, field, /*tQVar,*/ tPerm * p, condPerms * p, c2) {
                    quantifiedChunkHelper.splitLocations(σ, h2, field, tRcvr, tPerm * p, condPerms * p, c2) {
                      case Some((h3, ch, c3)) => Q(h3, ch.value, /*ch :: */Nil, c3)
                      case None => Failure[ST, H, S](pve dueTo InsufficientPermission(fa))
                    }

                  case false =>
                    Failure[ST, H, S](pve dueTo NonPositivePermission(loss))}})})}})

      case ast.AccessPredicate(fa @ ast.FieldAccess(eRcvr, field), perm)
          if quantifiedChunkHelper.isQuantifiedFor(h, field.name) =>

        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          evalp(σ, perm, pve, c1)((tPerm, c2) => {
            val condPerms = quantifiedChunkHelper.singletonConditionalPermissions(tRcvr, tPerm)
            quantifiedChunkHelper.splitSingleLocation(σ, h, field, tRcvr, tPerm * p, condPerms * p, c2) {
              case Some((h1, ch, c3)) => Q(h1, ch.value, /*ch :: */ Nil, c3)
              case None => Failure[ST, H, S](pve dueTo InsufficientPermission(fa))
            }}))

      case ast.AccessPredicate(locacc, perm) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          evalp(σ, perm, pve, c1)((tPerm, c2) =>
            decider.assert(σ, IsPositive(tPerm)){
              case true =>
                consumePermissions(σ, h, id, p * tPerm, locacc, pve, c2)((h1, ch, c3, results) => {
                  val c4 = c3.snapshotRecorder match {
                    case Some(sr) =>
                      c3.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(ch))))
                    case _ => c3}
                  ch match {
                    case fc: DirectFieldChunk =>
                      val snap = fc.value.convert(sorts.Snap)
                      Q(h1, snap, fc :: Nil, c4)

                    case pc: DirectPredicateChunk =>
                      val h2 =
                        if (results.consumedCompletely)
                          pc.nested.foldLeft(h1){case (ha, nc) => ha - nc}
                        else
                          h1
                      Q(h2, pc.snap, pc :: Nil, c4)}})

              case false =>
                Failure[ST, H, S](pve dueTo NonPositivePermission(perm))}))

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(φ))

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
			 * not in the partially consumed heap (h).
			 */
      case _ =>
        decider.tryOrFail[(H, Term, List[DirectChunk], C)](σ)((σ1, QS, QF) => {
          eval(σ1, φ, pve, c)((t, c) =>
            decider.assert(σ1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c))
              case false =>
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(φ)))
            })
        })(Q.tupled)
		}

		consumed
	}

  private def consumePermissions(σ: S,
                                 h: H,
                                 id: ChunkIdentifier,
                                 pLoss: P,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C)
                                (Q: (H, DirectChunk, C, PermissionsConsumptionResult) => VerificationResult)
                                :VerificationResult = {

    /* TODO: assert that pLoss > 0 */

    if (utils.consumeExactRead(pLoss, c)) {
      decider.withChunk[DirectChunk](σ, h, id, pLoss, locacc, pve, c)(ch => {
        if (decider.check(σ, IsNoAccess(ch.perm - pLoss))) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      decider.withChunk[DirectChunk](σ, h, id, locacc, pve, c)(ch => {
        assume(pLoss < ch.perm)
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
