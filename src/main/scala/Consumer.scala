package ch.ethz.inf.pm.silicon

import com.weiglewilczek.slf4s.Logging

import silAST.expressions.{Expression => SILExpression}
// import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}
import silAST.expressions.terms.{Term => SILTerm}

import interfaces.{Consumer, Evaluator, MapSupport, VerificationResult, Failure, 
		Success}
import interfaces.state.{Store, Heap, StateFormatter,
		PathConditions, State, StateFactory, /* PermissionFactory, */ PersistentChunk}
import interfaces.reporting.{Message, Reason}
import interfaces.decider.Decider
import state.terms._
// import state.terms.dsl._
import state.{/* CounterChunk, */ DefaultPredicateChunk, TypeConverter}
import reporting.ErrorMessages.{FractionMightBeNegative}
import reporting.Reasons.{ExpressionMightEvaluateToFalse, ReceiverMightBeNull,
		InsufficientPermissions, InsufficientLockchange, MethodLeavesDebt}
import reporting.{/* Consuming, ImplBranching, IfBranching, */ Bookkeeper}
import reporting.utils._
// import state.terms.utils.{¬, BigAnd}

trait DefaultConsumer[V, ST <: Store[V, ST],
											H <: Heap[H], PC <: PathConditions[PC],
											S <: State[V, ST, H, S]]
		extends Consumer[V, SILExpression, ST, H, S]
		{ this:      Logging
            with Evaluator[V, SILExpression, SILTerm, ST, H, S]
            with Brancher =>

	protected val decider: Decider[V, ST, H, PC, S]
  import decider.{fresh, assume}
	
	// protected val permissionFactory: PermissionFactory[P]
	// import permissionFactory._
	
	protected val typeConverter: TypeConverter
	import typeConverter.toSort
	
	// protected val mapSupport: MapSupport[ST, H, S]
	// import mapSupport.update

	protected val chunkFinder: ChunkFinder[H]
	import chunkFinder.{withFieldChunk, withPredicateChunk}
	
	// protected val lockSupport: LockSupport[ST, H, S]
	// protected val creditSupport: CreditSupport[ST, H, S]
	protected val stateFormatter: StateFormatter[V, ST, H, S, String]

	protected val bookkeeper: Bookkeeper
	protected val config: Config
	
	def consume(σ: S, p: PermissionTerm, φ: SILExpression, m: Message,
			Q: (S, Term) => VerificationResult): VerificationResult =

		consume2(σ, σ.h, p, φ, m, (h1, t) => {
			// logger.debug("\nconsume2'ed " + φ)
			// logger.debug("resulting S1 = " + π1)
			Q(σ \ h1, t)})
			
	protected def consume(σ: S, h: H, p: PermissionTerm, φ: SILExpression, m: Message,
			Q: (H, Term) => VerificationResult): VerificationResult =

		consume2(σ, h, p, φ, m, Q)
			
	protected def consume2(σ: S, h: H, p: PermissionTerm, φ: SILExpression, m: Message,
			Q: (H, Term) => VerificationResult): VerificationResult = {

		logger.debug("\nCONSUME " + φ.toString)
    logger.debug("  " + φ.getClass.getName)
		logger.debug(stateFormatter.format(σ))
		logger.debug("h = " + stateFormatter.format(h))
		
		val consumed = φ match {
			// case _ =>
				// logger.debug("consuming " + φ)
				// Success()
		
			/* And <: BooleanExpr */
			case silAST.expressions.BinaryExpression(_: silAST.symbols.logical.And, a0, a1) =>
				consume(σ, h, p, a0, m, (h1, s1) =>
					consume(σ, h1, p, a1, m, (h2, s2) =>
						Q(h2, Combine(s1, s2))))

			/* Implies <: BooleanExpr */
			case silAST.expressions.BinaryExpression(_: silAST.symbols.logical.Implication, e0, a1) /* if !φ.isPure */ =>
				evale(σ, e0, m, t0 =>
					branch(t0,
            consume(σ, h, p, a1, m, Q),
						Q(h, Unit)))

			// /* IfThenElse <: Expression */
			// case ast.IfThenElse(e0, a1, a2) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// branch(t0, c,
						// (c2: C) => consume(σ, h, p, a1, m, c2 + IfBranching(true, e0, t0), Q),
						// (c2: C) => consume(σ, h, p, a2, m, c2 + IfBranching(false, e0, t0), Q)))

			/* assert acc(e.f) */
			// case ast.Access(acc @ ast.FieldAccess(e0, id), p0) =>
      case silAST.expressions.PermissionExpression(rcvr, field, perm) =>
				evalt(σ, rcvr, m, tRcvr =>
					if (decider.assert(tRcvr ≠ Null()))
						evalp(σ, perm, m, tPerm => {
							// if (decider.isNonNegativeFraction(tPerm)) {
								val loss = tPerm * p
								withFieldChunk(h, tRcvr, field.name, loss, rcvr.toString, m at φ, fc => {
									val snap = fc.value.convert(sorts.Snap)
                  if (decider.assertNoAccess(fc.perm - loss)) {
                    val σ1 = σ \ (h - fc)
                    // if (id == "mu")
                      // update(σ1, lockSupport.Mu, tRcvr, c2, (σ2, c3) =>
                        // Q(σ2.h, snap, c3))
                    // else
                      Q(σ1.h, snap)}
                  else
                    Q(h - fc + (fc - loss), snap)})})
							// else
								// Failure(FractionMightBeNegative at φ withDetails (rcvr, field.name)))
					else
						Failure(m at rcvr dueTo ReceiverMightBeNull(rcvr.toString, field.name)))

			// /* assert acc(e.P) */
			// case ast.Access(ast.PredicateAccess(e0, id), p0) =>
				// val err = m at φ
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// evalp(σ, p0, m, c1, (pt, c2) =>
							// if (decider.isNonNegativeFraction(pt)) {
								// val loss = pt * p
								// withPredicateChunk(h, t0, id, loss, e0, err, c2, pc =>
									// if (decider.assertNoAccess(pc.perm - loss))
										// Q(h - pc, pc.snap, c2)
									// else
										// Q(h - pc + (pc - loss), pc.snap, c2))}
							// else
								// Failure(FractionMightBeNegative at φ withDetails (e0, id), c2))
					// else
						// Failure(m at e0 dueTo ReceiverMightBeNull(e0, id), c1))
            
      case qe @ silAST.expressions.QuantifierExpression(
                    silAST.symbols.logical.quantification.Exists(),
                    qvar,
                    silAST.expressions.BinaryExpression(
                        _: silAST.symbols.logical.And,
                        rdStarConstraints,
                        pe @ silAST.expressions.PermissionExpression(rcvr, field, _)))
           if toSort(qvar.dataType) == sorts.Perms =>

				evalt(σ, rcvr, m, tRcvr =>
					if (decider.assert(tRcvr ≠ Null()))
            withFieldChunk(h, tRcvr, field.name, rcvr.toString, m at φ, fc => {
              val witness = ast.utils.lv2pv(qvar).asInstanceOf[V]
              val tWitness = state.terms.Perms(decider.prover.fresh(qvar.name, sorts.Perms))
              val σ1 = σ \+ (witness, tWitness)
              evale(σ1, rdStarConstraints, m, tRdStarConstraints => {
                val tConstraints = state.terms.And(tRdStarConstraints, fc.perm > tWitness)
                assume(tConstraints,
                  Q(h - fc + (fc - tWitness), fc.value.convert(sorts.Snap)))})})
					else
						Failure(m at rcvr dueTo ReceiverMightBeNull(rcvr.toString, field.name)))

			// case ast.LockChangeExpr(ast.LockChange(es)) =>
				// assert(σ, h, φ, m, InsufficientLockchange, c, Q)
			
			// /* TODO: Extract together with Producer's case since they only differ
			 // *       in the operation (Minus here, Plus there).
			 // */
			// case ast.Credits(e0, e1) =>
				// /* Attention: Does not check if credits are greater than zero. */
				// eval(σ, e0, m, c, (tCh, c1) =>
					// if (decider.assert(tCh ≠ Null()))
						// eval(σ, e1, m, c1, (tN, c2) =>
							// update(σ \ h, creditSupport.Credits, tCh, c2, (σ1, c3) => {
								// val tc =
									// TermEq(
										// creditSupport.Credits(σ1.h, tCh),
										// Minus(
											// creditSupport.Credits(σ.h, tCh),
											// tN))
								// assume(tc, c3, (c4: C) =>
									// Q(σ1.h, Unit, c4))}))
					// else
						// Failure(m at e0 dueTo ReceiverMightBeNull("credit(" + e0 + ")"), c1))
						
			// case ast.DebtFreeExpr() =>
				// assert(σ, h, φ, m, MethodLeavesDebt, c, Q)
					
			// case (_: ast.MaxLockAtMost) | (_: ast.MaxLockLess) =>
				// assert(σ, h, φ, m, ExpressionMightEvaluateToFalse, c, Q)

			/* Any regular, pure expressions.
			 * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
			 * not in the partially consumed heap (h).
			 */
			case _ =>
				// assert(σ, h, φ, m, ExpressionMightEvaluateToFalse, Q)
      evale(σ, φ, m, t =>
        if (decider.assert(t))
          assume(t,
            Q(h, Unit))
        else {
          // println("\n[consume/_]")
          // println("  φ = " + φ)
          // println("  φ.sourceLocation = " + φ.sourceLocation)
          // println("  φ.sourceLocation = " + φ.sourceLocation.getClass.getName)
          // println("  m.text = " + m.text)
          Failure(m at φ dueTo ExpressionMightEvaluateToFalse)})
		}

		consumed
	}

	// private def assert(σ: S, h: H, e: ast.Expression, m: Message, r: Reason, c: C,
										 // Q: (H, Term, C) => VerificationResult): VerificationResult =

		// eval(σ \ updateCreditsRevision(σ.h, h), e, m, c, (t, c1) =>
			// if (decider.assert(t))
				// assume(t, c1, (c2: C) =>
					// Q(h, Unit, c2))
			// else
				// Failure(m at e dueTo r, c1))

	// private def updateCreditsRevision(hDest: H, hSrc: H): H = {
		// /* Consider the following preconditions:
		 // *
		 // *		class Test
		 // *			method muTest(x: Foo)
		 // *				requires acc(x.mu)
		 // *				requires waitlevel << x.mu
		 // *
		 // *			method creditTest(ch: AChannel)
		 // *				requires credit(ch, 1)
		 // *				requires waitlevel << ch.mu
		 // *
		 // * There are multiple pitfalls here when consuming callee's precondition:
		 // *
		 // * 1. Assume that waitlevel << x.mu holds at call-site of muTest.
		 // *    acc(x.mu) is consumed completely, with the result that the path
		 // *    condition mu-term mu(tx) is updated, i.e. the mu-function is updated
		 // *    for tx, and the mu-revision counter chunk is increased. The heap
		 // *    change is reflected in h, not in σ.h.
		 // *    If waitlevel << x.mu would now be asserted in h it would fail since
		 // *    mu(tx) has been havoced. Hence, the expression must be asserted in
		 // *    the unchanged σ.h.
		 // *    We could summarise this as "consuming acc(x.mu) has an effect on the
		 // *    result state h but not on the evaluation state σ.h".
		 // *
		 // * 2. Assume that waitlevel << ch.mu at call-site and that the current
		 // *    thread has zero credits for ch.
		 // *    When credit(ch, 1) is consumed the caller has -1 credits for ch.
		 // *    Semantically, this includes ch.mu in waitlevel and thus invalidates
		 // *    the previously holding waitlevel << ch.mu.
		 // *    Operationally, credit(ch, -1) results in an update to the
		 // *    credits-function credits(tch) and increases the corresponding revision 
		 // *    counter chunk, which is again reflected in h.
		 // *    If waitlevel << ch.mu is now asserted (consumed) in σ.h it will
		 // *    incorrectly hold, hence it must be asserted in h.
		 // *    We could summarise this as "consuming credit(ch, 1) has an effect on
		 // *    the result state h and also on the evaluation state σ.h".
		 // */
		
		// val gcs = hSrc.values.filter(_.id == "$Credits").toList
		// Predef.assert(gcs.length <= 1, "Expected to find at most one chunk with id $Credits.")

		// gcs.foldLeft(hDest){case (h, pc) => h + pc}
	// }
}