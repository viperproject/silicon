package ch.ethz.inf.pm.silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging

import silAST.expressions.{Expression => SILExpression}
// import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}

import interfaces.{Producer, Evaluator, VerificationResult, MapSupport, Failure, 
		Success}
import interfaces.decider.Decider
import interfaces.state.{Permission, Store, Heap, PathConditions, State, 
		StateFactory, StateFormatter, PersistentChunk, FieldChunk, 
		PredicateChunk, PermissionFactory, HeapMerger}
import interfaces.reporting.{Message}
import interfaces.state.factoryUtils.Ø
import state.terms.{Term, Combine, Null, IntSort, True, And, Or, LockMode, Plus,
		IntLiteral, TermEq, SnapEq}
import state.{TypeConverter}
// import ast.{Expression}
import state.{DefaultFieldChunk, DefaultPredicateChunk, CounterChunk}
import reporting.{/* Consuming, ImplBranching, IfBranching, IffBranching, */
		Bookkeeper}
// import reporting.utils._
import state.terms.utils.¬

/* TODO: Declare a ChunkFactory and use it to create FieldChunks and 
 *       PredicateChunks instead of directly creating e.g. DefaultFieldChunks.
 *       Use the factory in DefaultConsumer and DefaultExecuter, too.
 */

trait DefaultProducer[V, P <: Permission[P], ST <: Store[V, ST],
											H <: Heap[H], PC <: PathConditions[PC],
											S <: State[V, ST, H, S]]
		extends Producer[V, SILExpression, P, ST, H, S]
    with    HasLocalState
		{ this:      Logging
            with Evaluator[V, SILExpression, P, ST, H, S]
            with Brancher =>

	protected val decider: Decider[V, P, ST, H, PC, S]
	import decider.{fresh, assume}
	
	protected val stateFactory: StateFactory[V, ST, H, S]
	import stateFactory._
	
	protected val permissionFactory: PermissionFactory[P]
	import permissionFactory._

	protected val heapMerger: HeapMerger[H]
	import heapMerger.merge
	
	protected val typeConverter: TypeConverter
	import typeConverter.toSort
	
	// protected val mapSupport: MapSupport[ST, H, S]
	// import mapSupport.update
	
	// protected val lockSupport: LockSupport[ST, H, S]
	// protected val creditSupport: CreditSupport[ST, H, S]
	protected val stateFormatter: StateFormatter[V, ST, H, S, String]

	protected val bookkeeper: Bookkeeper
	protected val config: Config
	
	private var snapshotCacheFrames: Stack[Map[Term, (Term, Term)]] = Stack()
	private var snapshotCache: Map[Term, (Term, Term)] = Map()
	
	def produce(σ: S, s: Term, p: P, φ: SILExpression, m: Message,
			Q: S => VerificationResult): VerificationResult = {

			// produce2(σ, s, p, φ, m, c, (h, c1) =>
				// Q(σ \ h, c1))
			
		if (!config.selfFramingProductions) {
			produce2(σ, s, p, φ, m, h => {
				// Q(σ \ h, c1)})
				
				if (decider.checkSmoke)
					Success() /* TODO: Create smoke warning */
				else {
					val (mh, mts) = merge(Ø, h)
					assume(mts,
						Q(σ \ mh))}})
		} else  {
			val (pcs, npcs) = σ.h.values.partition(_.isInstanceOf[PersistentChunk])

			/* Persistent chunks (pcs) have to remain in the heap, all other
			 * chunks (npcs) are finally merged with the newly produced chunks.
			 */
			produce2(σ \ (h = H(pcs)), s, p, φ, m, h =>
				if (decider.checkSmoke)
					Success() /* TODO: Create smoke warning */
				else {
					val (mh, mts) = merge(H(npcs), h)
					assume(mts,
						Q(σ \ mh))})
		}
	}

	private def produce2(σ: S, s: Term, p: P, φ: SILExpression, m: Message,
			Q: H => VerificationResult): VerificationResult = {
			
		logger.debug("\nPRODUCE " + φ.toString)
		logger.debug(stateFormatter.format(σ))
		
		val produced = φ match {
			case _ =>
				logger.debug("Producing " + φ)
				Success()
				
			// /* And <: BooleanExpr */
			// case ast.And(a0, a1) =>
				// /* TODO: A lot of these snapshot are never used, they'll only polute
				 // *       the path conditions and thus increase the workload.
				 // */

        // // /* Might not be worth the effort, at least for the test suite
         // // * the Combine-case occurs only about 40 times.
         // // */
        // // val (tSnapEq, s0, s1) = s match {
          // // /* Scala (2.8.0) doesn't seem to like unicode characters in tuple
           // // * unpackings ... darn!
           // // */
          // // case Combine(sl, sr) =>
            // // // logger.error("[xxx COMBINE xxx]")
            // // (True(), sl, sr)
          // // case _ =>
            // // // logger.error("[xxx FRESH xxx]")
            // // val (sl, sr) = (fresh, fresh)
            // // (SnapEq(s, Combine(sl, sr)), sl, sr)}

				// val (s0, s1) =
					// if (snapshotCache.contains(s)) {
						// logger.debug("[Produce(And)] Took cache entry for snapshot " + s)
						// val (sl, sr) = snapshotCache(s)
						// (sl, sr)}
					// else {
						// val s0 = fresh
						// val s1 = fresh
						// if (config.cacheSnapshots) snapshotCache += (s -> (s0, s1))
						// (s0, s1)}
				
				// // val (s0, s1) = (fresh, fresh)
				
				// val tSnapEq = SnapEq(s, Combine(s0, s1))
				
				// assume(tSnapEq, c, (c1: C) =>
					// produce2(σ, s0, p, a0, m, c1, (h1, c2) =>
						// produce2(σ \ h1, s1, p, a1, m, c2, (h2, c3) =>
							// Q(h2, c3))))

			// /* Implies <: BooleanExpr */
			// case ast.Implies(e0, a0) if !φ.isPure =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// branch(t0, c,
						// (c2: C) => produce2(σ, s, p, a0, m, c2 + ImplBranching(true, e0, t0), Q),
						// (c2: C) => Q(σ.h, c2 + ImplBranching(false, e0, t0))))			
			
			// /* Iffs currently cannot be handled by the evaluator:
			 // *  - Assume a method such as
			 // *      method m()
			 // *        requires ... && b <==> c1 == c2 && acc(c1.x, 50) && acc(c2.x, 50)
			 // *      {
			 // *        if (b) then {
			 // *          assert acc(c1.x, 100)
			 // *        }
			 // *      }
			 // *  - The evaluator would yield a term tb <==> tc1 == tc2 which is added to
			 // *    the path conditions
			 // *  - Producing acc(c1.x, 50) && acc(c2.x, 50) yields two corresponding chunks
			 // *  - In the if-branch tb == true is assumed, but no heap merg is down and thus
			 // *    the assertion fails.
			 // */
			// /* Iff <: BooleanExpr */
			// case ast.Iff(e1, e2) =>
				// eval(σ, e1, m, c, (t1, c1) =>
					// eval(σ, e2, m, c1, (t2, c2) =>
						// branch(t1 :: t2 :: Nil, c1,
							// (c3: C) => Q(σ.h, c3 + IffBranching(true, φ, t1, t2)),
							// (c3: C) => Q(σ.h, c3 + IffBranching(false, φ, t1, t2)))))

			// /* IfThenElse <: Expression */
			// case ast.IfThenElse(e0, a1, a2) if !φ.isPure =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// branch(t0, c,
						// (c2: C) => produce2(σ, s, p, a1, m, c2 + IfBranching(true, e0, t0), Q),
						// (c2: C) => produce2(σ, s, p, a2, m, c2 + IfBranching(false, e0, t0), Q)))

			// /* assume acc(e.f) */
			// case ast.Access(acc @ ast.FieldAccess(e0, id), p0) =>
				// assert(acc.f !=  null, /* @elidable */
						// "Expected FieldAccess.f to be non-null.")
				// assert(acc.f.typ !=  null, /* @elidable */
						// "Expected FieldAccess.f.typ to be non-null.")
				// assert(acc.f.typ.typ !=  null, /* @elidable */
						// "Expected FieldAccess.f.typ.typ to be non-null.")
				
				// eval(σ, e0, m, c, (t0, c1) =>
					// assume(t0 ≠ Null(), c1, (c2: C) =>
						// evalp(σ, p0, m, c2, (gain, c3) =>
							// decider.isValidFraction(gain) match {
								// case None =>								
									// val snap = s.convert(IntSort, toSort(acc.f.typ))
									// val fc = DefaultFieldChunk(t0, id, snap, gain * p)
									// val tMu =
										// if (id == "mu") lockSupport.Mu(σ.h, t0, snap)
										// else True()
									// val (mh, mts) = merge(σ.h, H(fc :: Nil))
									// assume(mts + tMu, c3, (c4: C) =>
										// Q(mh, c4))
								// case Some(errmsg) =>
									// Failure(errmsg at φ withDetails (e0, id), c3)})))

			// /* assume acc(e.P) */
			// case ast.Access(ast.PredicateAccess(e0, id), p0) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// assume(t0 ≠ Null(), c1, (c2: C) =>
						// evalp(σ, p0, m, c2, (gain, c3) =>
							// decider.isValidFraction(gain) match {
								// case None =>
									// val pc = DefaultPredicateChunk(t0, id, s, gain * p)
									// val (mh, mts) = merge(σ.h, H(pc :: Nil))
									// assume(mts, c3, (c4: C) =>
										// Q(mh, c4))
								// case Some(errmsg) =>
									// Failure(errmsg at φ withDetails (e0, id), c3)})))

			// /* TODO: More complex assertions involving holds, e.g. '!!holds(c)'
			 // *       might not work because they don't match here.
			 // */
			// case ast.Not(ast.Holds(e0, p0)) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// update(σ, lockSupport.Holds, t0, c1, (σ1, c2) =>
						// assume(lockSupport.Holds(σ1.h, t0, LockMode.None), c2, (c3: C) =>
							// Q(σ1.h, c3))))
			
			// case ast.Holds(e0, p0) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// update(σ, lockSupport.Holds, t0, c1, (σ1, c2) =>
						// assume(lockSupport.Holds(σ1.h, t0, evallm(p0)), c2, (c3: C) =>
							// Q(σ1.h, c3))))
						
			// /* TODO: Extract together with Consumer's case since they only differ
			 // *       in the operation (Plus here, Minus there).
			 // */
			// case ast.Credits(e0, e1) =>
				// eval(σ, e0, m, c, (tCh, c1) =>
					// assume(tCh ≠ Null(), c1, (c2: C) =>
						// eval(σ, e1, m, c2, (tN, c3) =>
							// update(σ, creditSupport.Credits, tCh, c3, (σ1, c4) => {
								// val tc =
									// TermEq(
										// creditSupport.Credits(σ1.h, tCh),
										// Plus(
											// creditSupport.Credits(σ.h, tCh),
											// tN))
								// assume(tc, c4, (c5: C) =>
									// Q(σ1.h, c5))}))))
						
			// case ast.DebtFreeExpr() =>
				// /* Should only be produced when well-definedness is checked, hence
				 // * equivalent to skip.
				 // */
				// Q(σ.h, c)

			// /* Any regular expressions, i.e. boolean and arithmetic. */
			// case _ =>
				// eval(σ, φ, m, c, (t, c1) => {
					// t.setSrcPos(m.loc)
						// /* TODO: Taking the position from the message - which is not
						 // * necessarily set at this time - enables smoke warnings that
						 // * e.g. give the line number of a method invocation where invoked
						 // * method's postcondition is equivalent to false.
						 // *
						 // * This is rather hacky and one should consider completely changing
						 // * the way line numbers are tracked.
						 // *
						 // * Idea: Add a list of Positions (line numbers) to the context.
						 // * When executing a call statement the call site position p1 is
						 // * appended to the context's list. When creating a Warning or a
						 // * Failure the current context's list suffixed with the current
						 // * position p2 is passed to msg.at. When formatting the msg
						 // * the list is eventually used to fill all %s of
						 // * Message.toString + Reason(s).toString.
						 // */
					// assume(t, c1, (c2: C) =>
						// Q(σ.h, c2))})
		}

		produced
	}
	
	override def pushLocalState() {
		snapshotCacheFrames = snapshotCacheFrames.push(snapshotCache)
		super.pushLocalState()
	}
	
	override def popLocalState() {
		snapshotCache = snapshotCacheFrames.top
		snapshotCacheFrames = snapshotCacheFrames.pop
		super.popLocalState()
	}
}