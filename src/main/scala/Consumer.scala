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
import silver.verifier.reasons.{NegativePermission, AssertionFalse}
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import reporting.Bookkeeper
import state.{DirectChunk, DefaultContext}
import state.terms._
import supporters.{LetHandler, Brancher, ChunkSupporter}

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



  /** Wrapper Method for consume, for logging. See Executor.scala for explanation of analogue. **/
  protected def consume(σ: S, h: H, p: Term, φ: ast.Exp, pve: PartialVerificationError, c: C)
                       (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {
    val SEP_identifier = SymbExLogger.currentLog().insert(new ConsumeRecord(φ, σ, c))
    consume2(σ, h, p, φ, pve, c)((h1, t1, l1, c1) => {
      SymbExLogger.currentLog().collapse(φ, SEP_identifier)
      Q(h1, t1, l1, c1)})
  }

  protected def consume2(σ: S, h: H, p: Term, φ: ast.Exp, pve: PartialVerificationError, c: C)
                       (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
    }

    val consumed = φ match {
      case ast.And(a1, a2) if !φ.isPure || config.handlePureConjunctsIndividually() =>
        consume(σ, h, p, a1, pve, c)((h1, s1, dcs1, c1) =>
          consume(σ, h1, p, a2, pve, c1)((h2, s2, dcs2, c2) => {
            Q(h2, Combine(s1, s2), dcs1 ::: dcs2, c2)}))

      case imp @ ast.Implies(e0, a0) if !φ.isPure =>
        val impLog = new GlobalBranchRecord(imp, σ, c, "consume")
        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
        SymbExLogger.currentLog().initializeBranching()

        eval(σ, e0, pve, c)((t0, c1) => {
          impLog.finish_cond()
          val branch_res = branch(σ, t0, c1,
            (c2: C) => consume(σ, h, p, a0, pve, c2)((h_a1, s_a1, dc_a1, c_a1) => {
              val res1 = Q(h_a1, s_a1, dc_a1, c_a1)
              impLog.finish_thnSubs()
              SymbExLogger.currentLog().prepareOtherBranch(impLog)
              res1}),
            (c2: C) => {
              val res2 = Q(h, Unit, Nil, c2)
              impLog.finish_elsSubs()
              res2})
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

      case ite @ ast.CondExp(e0, a1, a2) if !φ.isPure =>
        val gbLog = new GlobalBranchRecord(ite, σ, c, "consume")
        val sepIdentifier = SymbExLogger.currentLog().insert(gbLog)
        SymbExLogger.currentLog().initializeBranching()

        eval(σ, e0, pve, c)((t0, c1) => {
          gbLog.finish_cond()
          val branch_res = branch(σ, t0, c1,
            (c2: C) => consume(σ, h, p, a1, pve, c2)((h_a1, s_a1, dc_a1, c_a1) => {
              val res1 = Q(h_a1, s_a1, dc_a1, c_a1)
              gbLog.finish_thnSubs()
              SymbExLogger.currentLog().prepareOtherBranch(gbLog)
              res1}),
            (c2: C) => consume(σ, h, p, a2, pve, c2)((h_a2, s_a2, dc_a2, c_a2) => {
              val res2 = Q(h_a2, s_a2, dc_a2, c_a2)
              gbLog.finish_elsSubs()
              res2}))
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})

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
}
