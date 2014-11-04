/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.verifier.{VerificationError, PartialVerificationError}
import silver.verifier.reasons.{NamedMagicWandChunkNotFound, NonPositivePermission, AssertionFalse,
    MagicWandChunkNotFound}
import interfaces.state.{Store, Heap, PathConditions, State, Chunk, StateFactory, StateFormatter, ChunkIdentifier}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.state.factoryUtils.Ø
import reporting.Bookkeeper
import viper.silicon.state.{DefaultContext, DirectChunk, DirectFieldChunk, DirectPredicateChunk, MagicWandChunk,
    MagicWandChunkIdentifier}
import state.terms._
import state.terms.perms.{IsPositive, IsNoAccess}
import supporters.MagicWandSupporter

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S]]
		extends Consumer[DefaultFractionalPermissions, Chunk, ST, H, S, DefaultContext[H]]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[H]]
									  with Brancher[ST, H, S, DefaultContext[H]]
                    with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[H]]
                    with MagicWandSupporter[ST, H, PC, S] =>

  private type C = DefaultContext[H]
  private type P = DefaultFractionalPermissions
  private type CH = Chunk

  protected implicit val manifestH: Manifest[H]

  protected val decider: Decider[P, ST, H, PC, S, C]
  import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
//  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C]
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
             (Q: (S, Term, List[CH], C) => VerificationResult)
             : VerificationResult = {

    consume(σ, σ.h, p, φ.whenExhaling, pve, c)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))
  }

  def consumes(σ: S,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C)
              (Q: (S, Term, List[CH], C) => VerificationResult)
              : VerificationResult =

    consumes(σ, σ.h, p, φs map (_.whenExhaling), pvef, c)(Q)

  private def consumes(σ: S,
                       h: H,
                       p: P,
                       φs: Seq[ast.Expression],
                       pvef: ast.Expression => PartialVerificationError,
                       c: C)
                       (Q: (S, Term, List[CH], C) => VerificationResult)
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
                       (Q: (H, Term, List[CH], C) => VerificationResult)
                       : VerificationResult = {

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nCONSUME ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
      logger.debug("h = " + stateFormatter.format(h))
      if (c.reserveHeaps.nonEmpty)
        logger.debug("hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
//      c.lhsHeap.map(h => logger.debug("hLHS = " + stateFormatter.format(h)))
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
        val σC = combine(σ, h, c)
				eval(σC, e0, pve, c)((t0, c1) =>
					branch(σC, t0, c1,
						(c2: C) => consume(σ, h, p, a0, pve, c2)(Q),
						(c2: C) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        val σC = combine(σ, h, c)
        eval(σC, e0, pve, c)((t0, c1) =>
          branch(σC, t0, c1,
            (c2: C) => consume(σ, h, p, a1, pve, c2)(Q),
            (c2: C) => consume(σ, h, p, a2, pve, c2)(Q)))

      case ast.AccessPredicate(locacc, perm) =>
        val σC = combine(σ, h, c)
        withChunkIdentifier(σC, locacc, true, pve, c)((id, c1) =>
          evalp(σC, perm, pve, c1)((tPerm, c2) =>
            decider.assert(σC, perms.IsMaybePositive(tPerm) /*IsPositive(tPerm)*/){
              case true =>
                consumePermissions(σC, h, id, p * tPerm, locacc, pve, c2)((h1, ch, c3, results) => {
                  val c4 = c3.snapshotRecorder match {
                    case Some(sr) =>
                      c3.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(ch.id))))
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

      /* Handle wands or wand-typed variables */
      case _ if φ.typ == ast.types.Wand && magicWandSupporter.isDirectWand(φ) =>
        /* Resolve wand and get mapping from (possibly renamed) local variables to their values. */
//        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, φ)
//        val σC = combine(σ \+ Γ(wandValues), h, c)

        /* Checks that the value of package-old expressions hasn't changed
         * w.r.t. the state in which the wand was produced.
         *
         * TODO: It would be nice if this method could be moved into the MagicWandSupporter,
         *       but it is not obvious how to call eval(...) from there.
         *       This would be possible if MagicWandSupporter were a trait whose self-type
         *       required it to be mixed into an Evaluator.
         */
//        def reinterpret(ch: MagicWandChunk, c: C)
//                       (Q: C => VerificationResult)
//                       : VerificationResult = {
//
//          /* Collect pold-expressions together with conditional guards they are nested in.
//           * For example, b ==> pold(e) will be returned as (b, pold(e)).
//           */
//          val pathConditionedPOlds = magicWandSupporter.pathConditionedPOlds(wand)
//          /* Extract e from pold(e) and turn the list of pairs (b, pold(e)) into a list
//           * of terms of the shape b && e == pold(e).
//           */
//          val eqs = pathConditionedPOlds.map{case (pc, po) =>
//            val eq = ast.Equals(po.exp, po)(po.pos, po.info)
//            ast.Implies(pc, eq)(pc.pos, pc.info)
//          }
//          val eSame = ast.utils.BigAnd(eqs)
//          /* Check the generated equalities. */
//          eval(σC, eSame, pve, c/*.copy(poldHeap = Some(ch.hPO))*/)((tSame, c1) =>
//            decider.assert(σC, tSame) {
//              case true =>
//                Q(c1/*.copy(poldHeap = c.poldHeap)*/)
//              case false =>
//                Failure[ST, H, S](pve dueTo MagicWandChunkOutdated(wand))})
//        }

//        /* TODO: Getting id by first creating a chunk is not elegant. */
//        val id = magicWandSupporter.createChunk(σC.γ, /*σC.h,*/ wand).id

        def QL(σ: S, id: MagicWandChunkIdentifier, ve: VerificationError, c: C) = {
          val σC = combine(σ /*\+ Γ(wandValues)*/, h, c)
          val hs =
            if (c.exhaleExt) c.reserveHeaps
            else Stack(h)

          magicWandSupporter.doWithMultipleHeaps(hs, c)((h1, c1) =>
            decider.getChunk[MagicWandChunk](σC, h1, id, c1) match {
              case someChunk @ Some(ch) => (someChunk, h1 - ch, c1)
              case _ => (None, h1, c1)
            }
          ){case (Some(ch), hs1, c1) =>
            assert(c1.exhaleExt == c.exhaleExt)
            if (c.exhaleExt) {
              /* transfer: move ch into h = σUsed*/
              assert(hs1.size == c.reserveHeaps.size)
              Q(h + ch, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs1))
            } else {
              assert(hs1.size == 1)
              assert(c.reserveHeaps == c1.reserveHeaps)
              Q(hs1.head, decider.fresh(sorts.Snap), List(ch), c1)
            }

          //            if (!c.reinterpretWand)
          //              Q(hs.head, decider.fresh(sorts.Snap), List(ch), c1.copy(reserveHeaps = hs.tail))
          //            else
          //              reinterpret(ch, c1.copy(reserveHeaps = hs.tail))(c2 =>
          //                Q(hs.head, decider.fresh(sorts.Snap), List(ch), c2))
          case _ =>
//            Failure[ST, H, S](pve dueTo MagicWandChunkNotFound(wand))
            Failure[ST, H, S](ve)
          }
        }

        φ match {
          case wand: ast.MagicWand =>
//            eval(σ, wand, pve, c)((tWand, c1) => {
            magicWandSupporter.createChunk(σ, wand, pve, c)((chWand, c1) => {
              val ve = pve dueTo MagicWandChunkNotFound(wand)
              QL(σ, chWand.id, ve, c1)})
          case v: ast.LocalVariable =>
            val tWandChunk = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
            val ve = pve dueTo NamedMagicWandChunkNotFound(v)
            QL(σ, tWandChunk.id, ve, c)
          case _ => sys.error(s"Expected a magic wand, but found node $φ")
        }

      case pckg @ ast.Packaging(eWand, eIn) =>
//        val pve = PackagingFailed(pckg)
        /* TODO: Creating a new error reason here will probably yield confusing error
         *       messages if packaging fails as part of exhaling a method's precondition
         *       during a method call.
         *       I expected the error message to be "Packaging ... failed because ... (line N)",
         *       where N denotes the line in which the method precondition can be found.
         *       The message should be "Method ... failed because packaging failed ... because ...
         */
        val σEmp = Σ(σ.γ, Ø, σ.g)
        val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
        decider.locally[(H, Term, List[CH], C)](QB => {
          produce(σEmp, decider.fresh, FullPerm(), eWand.left, pve, c0)((σLhs, c1) => {
            val c2 = c1.copy(reserveHeaps = c.reserveHeaps.head +: σLhs.h +: c.reserveHeaps.tail, exhaleExt = true)
            val rhs = eWand.right
            consume(σEmp, σEmp.h, FullPerm(), rhs, pve, c2)(scala.Function.untupled(QB))})} /* exhale_ext */
        ){case (_, _, _, c1) => /* result of exhale_ext, h1 = σUsed' */
            magicWandSupporter.createChunk(σ, eWand, pve, c1)((chWand, c3) => {
              val h2 = h + chWand /* h2 = σUsed'' */
              val σEmp = Σ(σ.γ, Ø, σ.g)
              val c4 = c3.copy(reserveHeaps = (c3.reserveHeaps.head + h2) +: c3.reserveHeaps.drop(2),
                               exhaleExt = c.exhaleExt)
              consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4)((h3, _, _, c5) =>
                Q(h3, decider.fresh(sorts.Snap), Nil, c5))})}

      case ast.Applying(eWandOrVar, eIn) =>
//        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, eWandOrVar)
        val (eWand, eLHSAndWand) = eWandOrVar match {
          case _eWand: ast.MagicWand =>
            (_eWand, ast.And(_eWand.left, _eWand)(_eWand.left.pos, _eWand.left.info))
          case v: ast.LocalVariable =>
            val tWandChunk = σ.γ(v).asInstanceOf[MagicWandChunkTerm].chunk
            val _eWand = tWandChunk.ghostFreeWand
            (_eWand, ast.And(_eWand.left, v)(v.pos, v.info))
          case _ => sys.error(s"Expected a magic wand, but found node $φ")
        }

        val σWV = σ //\+ Γ(wandValues)
        val σEmp = Σ(σ.γ, Ø, σ.g)
//        val eLHSAndWand = ast.And(eWandOrVar.left, eWandOrVar)(eWandOrVar.left.pos, eWandOrVar.left.info)
//        println(s"eLHSAndWand = $eLHSAndWand")
        consume(σEmp \ σWV.γ, h, FullPerm(), eLHSAndWand, pve, c/*.copy(reinterpretWand = false)*/)((h1, _, chs1, c1) => { /* exhale_ext, h1 = σUsed' */
//          println(s"chs1 = $chs1")
          assert(chs1.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
          val ch = chs1.last.asInstanceOf[MagicWandChunk]
          val c1a = c1.copy(reserveHeaps = Nil, exhaleExt = false)/*.copy(reinterpretWand = c.reinterpretWand)*/
          consume(σWV \ h1, h1, FullPerm(), eLHSAndWand, pve, c1a/*.copy(reinterpretWand = false)*/)((h2, _, chs2, c2) => { /* σUsed'.apply */
            assert(chs2.last.isInstanceOf[MagicWandChunk], s"Unexpected list of consumed chunks: $chs1")
            assert(ch == chs2.last.asInstanceOf[MagicWandChunk], s"Expected $chs1 == $chs2")
            val c2a = c2.copy(lhsHeap = Some(h1))
            produce(σWV \ h2, decider.fresh, FullPerm(), eWand.right, pve, c2a)((σ3, c3) => { /* σ3.h = σUsed'' */
              val c3a = c3.copy(reserveHeaps = (c1.reserveHeaps.head + σ3.h) +: c1.reserveHeaps.tail,
                                exhaleExt = c1.exhaleExt,
                                lhsHeap = c2.lhsHeap)
              decider.prover.logComment(s"in consume/apply after producing RHS ${eWand.right}}, before consuming $eIn")
              consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c3a)((h4, _, _, c4) =>
                Q(h4, decider.fresh(sorts.Snap), Nil, c4))})})})

      case ast.Folding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) =>

        val predicate = c.program.findPredicate(predicateName)
        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0 = c.incCycleCounter(predicate)
          val σC = combine(σ, h, c0)
          val σEmp = Σ(σ.γ, Ø, σ.g)
          evalp(σC, ePerm, pve, c0)((tPerm, c1) => {
            if (decider.check(σC, IsPositive(tPerm)))
              evals(σC, eArgs, pve, c1)((tArgs, c2) => {
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs) /* TODO: Substitute args in body */
                consume(σEmp \ insγ, h, FullPerm(), predicate.body, pve, c2)((h1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
                  val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false, additionalEvalHeap = Some(c3.reserveHeaps.head))
                  consume(σ \ h1 \ insγ, h1, FullPerm(), predicate.body, pve, c3a)((h2, snap, _, c3b) => { /* σUsed'.fold */
                    produce(σ \ h2, s => snap.convert(s), tPerm, acc, pve, c3b)((σ2, c4) => { /* σ2.h = σUsed'' */
                      val c4a = c4.decCycleCounter(predicate)
                                  .copy(reserveHeaps = (c3.reserveHeaps.head + σ2.h) +: c3.reserveHeaps.tail,
                                        exhaleExt = c3.exhaleExt,
                                        additionalEvalHeap = c3.additionalEvalHeap)
                      consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4a)((h3, _, _, c5) =>
                        Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})})})
            else
              Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm))})
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> folding next.P in e} is currently not " +
            "supported. It should be  possible to wrap 'folding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + φ)

      case ast.Unfolding(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm),
                       eIn) if c.exhaleExt && !φ.isPure =>

        val predicate = c.program.findPredicate(predicateName)
        if (c.cycles(predicate) < 2 * config.unrollFunctions()) {
          val c0 = c.incCycleCounter(predicate)
          val σC = combine(σ, h, c0)
          val σEmp = Σ(σ.γ, Ø, σ.g)
          evalp(σC, ePerm, pve, c0)((tPerm, c1) =>
            if (decider.check(σC, IsPositive(tPerm)))
              evals(σC, eArgs, pve, c1)((tArgs, c2) =>
                consume(σEmp, h, FullPerm(), acc, pve, c2)((h1, _, _, c3) => { /* exhale_ext, h1 = σUsed' */
                  val c3a = c3.copy(reserveHeaps = Nil, exhaleExt = false, additionalEvalHeap = Some(c3.reserveHeaps.head))
                  consume(σ \ h1, h1, FullPerm(), acc, pve, c3a)((h2, snap, _, c3b) => { /* σUsed'.unfold */
                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                    produce(σ \ h2 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3b)((σ2, c4) => { /* σ2.h = σUsed'' */ /* TODO: Substitute args in body */
                      val c4a = c4.decCycleCounter(predicate)
                                  .copy(reserveHeaps = (c3.reserveHeaps.head + σ2.h) +: c3.reserveHeaps.tail,
                                        exhaleExt = c3.exhaleExt,
                                        additionalEvalHeap = c3.additionalEvalHeap)
                      consume(σEmp, σEmp.h, FullPerm(), eIn, pve, c4a)((h3, _, _, c5) =>
                        Q(h3, decider.fresh(sorts.Snap), Nil, c5))})})}))
            else
              Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm)))
        } else
          sys.error("Recursion that does not go through a function, e.g., a predicate such as " +
            "P {... && next != null ==> unfolding next.P in e} is currently not " +
            "supported. It should be  possible to wrap 'unfolding next.P in e' " +
            "in a function, which is then invoked from the predicate body.\n" +
            "Offending node: " + φ)

			/* Any regular Expressions, i.e. boolean and arithmetic */
      case _ =>
        val σC = combine(σ, h, c)
        val c0 = c.copy(reserveHeaps = Nil, exhaleExt = false)
        decider.tryOrFail[(H, Term, List[CH], C)](σC, c0)((σC1, QS, QF) => {
          eval(σC1, φ, pve, c0)((t, c1) =>
            decider.assert(σC1, t) {
              case true =>
                assume(t)
                QS((h, Unit, Nil, c1.copy(reserveHeaps = c.reserveHeaps, exhaleExt = c.exhaleExt)))
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
                                : VerificationResult = {

    /* TODO: Integrate into regular, (non-)exact consumption that follows afterwards */
    if (c.exhaleExt) /* Function "transfer" from wands paper */
      /* Permissions are transferred from the stack of heaps to σUsed, which is h in the current context */
      return magicWandSupporter.consumeFromMultipleHeaps(σ, c.reserveHeaps, id, pLoss, locacc, pve, c)((hs, chs, c1/*, pcr*/) => {
        val c2 = c1.copy(reserveHeaps = hs)
        val pcr = PermissionsConsumptionResult(false) // TODO: PermissionsConsumptionResult is bogus!
        Q(h + H(chs), chs.head, c2, pcr)})

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

  /* TODO: Remove and use DefaultContext.additionalEvalHeap instead.
   *       On the other hand, if additionalEvalHeap is only necessary
   *       to evaluate receivers when executing σUsed'.(un)fold, then it might
   *       be better to do as suggested in the formalisation, that is, to
   *       replace the formal arguments with terms, for example
   *         σUsed'.fold(P(t))
   *       where t := eval(e) if P(e).
   *       */
  private def combine(σ: S, h: H, c: C): S = {
    val hCombined = c.reserveHeaps.headOption.fold(σ.h)(h + _)
    σ \ hCombined
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
