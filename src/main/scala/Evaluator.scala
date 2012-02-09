package ch.ethz.inf.pm.silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging

import silAST.expressions.{Expression => SILExpression}
import silAST.programs.symbols.{Function => SILFunction}
import silAST.expressions.terms.{LiteralTerm => SILLiteral}
// import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}

import interfaces.{Evaluator, Consumer, Producer, VerificationResult,
		Failure, Success}
import interfaces.state.{Permission, Store, Heap, PathConditions, State, 
		StateFormatter, StateFactory, PermissionFactory, HeapMerger}
import interfaces.decider.Decider
import interfaces.reporting.{Message}
// import interfaces.ast.specialVariables
// import interfaces.ast.specialVariables.This
import interfaces.state.factoryUtils.Ø
/*
import ast.{Expression, Variable, FieldAccess, Old, ArithmeticExpr,
		CompareExpr, BooleanExpr, VariableExpr, ThisExpr, FunctionApplication, 
		IfThenElse, Unfolding, Access, PredicateAccess, SeqQuantification, RangeSeq,
		ExplicitSeq, EmptySeq, SeqLength, SeqCon, SeqAt, SeqIn, SeqTake, SeqDrop,
		TypeQuantification, IntType}
*/
import state.{/* FractionalPermission, */ TypeConverter, CounterChunk}
import state.terms
import state.terms.{Term, Null}
import reporting.ErrorMessages.{InvocationFailed, UnfoldingFailed, 
		FractionMightBeNegative}
import reporting.Reasons.{ReceiverMightBeNull, InsufficientPermissions}
import reporting.{/* Evaluating, IfBranching, ImplBranching, */ Bookkeeper}
import reporting.utils._
import state.terms.utils.¬

trait DefaultEvaluator[V, P <: Permission[P], ST <: Store[V, ST], H <: Heap[H],
											 PC <: PathConditions[PC], S <: State[V, ST, H, S]]
		extends Evaluator[V, SILExpression, P, ST, H, S]
		with    HasLocalState
		{ this:      Logging
            with Consumer[V, SILExpression, P, ST, H, S]
            with Producer[V, SILExpression, P, ST, H, S] =>

	protected val decider: Decider[V, P, ST, H, PC, S]
	import decider.{fresh, assume}
										
	protected val stateFactory: StateFactory[V, ST, H, S]
	import stateFactory._
	
	protected val permissionFactory: PermissionFactory[P]
	import permissionFactory._
	
	//protected val lockSupport: LockSupport[ST, H, S]
	//protected val creditSupport: CreditSupport[ST, H, S]
	
	protected val typeConverter: TypeConverter
	import typeConverter.toSort
	
	protected val chunkFinder: ChunkFinder[SILExpression, P, H]
	import chunkFinder.withFieldChunk
	
	protected val stateFormatter: StateFormatter[V, ST, H, S, String]

	protected val config: Config
	protected val bookkeeper: Bookkeeper
	
	// protected var thisClass: ast.Class
	
	private var fappCache: Map[Term, Set[Term]] = Map()
	private var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()
	
	def evals(σ: S, es: List[SILExpression], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult =

		evals2(σ, es, Nil, m, ts =>
			Q(ts))
			
	def eval(σ: S, e: SILExpression, m: Message,
					 Q: Term => VerificationResult): VerificationResult =
			
		eval(σ, Nil, e, m, t =>
			Q(t))
	
	// /* TODO: If we move permission evaluation into a dedicated class we could
	 // *       implement the DefaultEvaluator for any P <: Permission[P].
	 // */
	// def evalp(σ: S, p: ast.FractionalPermission, m: Message,
			// Q: FractionalPermission => VerificationResult) = p match {
			
		// case ast.ConstFraction(per, eps) =>
			// Q(state.ConstFraction(per, eps))

		// case ast.ExprFraction(per, eps) =>
			// eval(σ, Nil, per, m, tPer =>
				// eval(σ, Nil, eps, m, tEps =>
					// Q(state.TermFraction(tPer, tEps))))
	// }
			
	private def evals2(σ: S, es: List[SILExpression], ts: List[Term], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult = {

		if (es.isEmpty)
			Q(ts.reverse)
		else
			eval(σ, Nil, es.head, m, t =>
				evals2(σ, es.tail, t :: ts, m, Q))
	}
	
	def evall(lit: SILLiteral): Term = lit match {
		case _ =>
			logger.debug("Evaluating literal " + lit)
			null
		// case ast.Null() => terms.Null()
		// case ast.True() => terms.True()
		// case ast.False() => terms.False()
		// case ast.IntLiteral(n) => terms.IntLiteral(n)
		// // case ast.MaxLock() => terms.MaxLock
		// case ast.BottomLock() => terms.BottomLock()
		// case ast.EmptySeq(_) => terms.EmptySeq()
		// case ast.FreshLiteral => fresh
			// /* TODO: Parameterise FreshLiteral with expected type */
	}
	
	// def evallm(lm: ast.LockMode): terms.LockMode = lm match {
		// case ast.ReadLockMode => terms.LockMode.Read
		// case ast.WriteLockMode => terms.LockMode.Write
	// }
	
	protected def eval(σ: S, cs: List[SILFunction], e: SILExpression, m: Message, 
			Q: Term => VerificationResult): VerificationResult =
			
		eval2(σ, cs, e, m, t => {
			t.setSrcNode(e)
			Q(t)})
	
	/* Attention: Only use eval(σ, cs, e, m, c Q) inside of eval2, because
	 *   - eval adds an "Evaluating" operation to the context
	 *   - eval sets the source node of the resulting term
	 */
	protected def eval2(σ: S, cs: List[SILFunction], e: SILExpression, m: Message, 
			Q: Term => VerificationResult): VerificationResult = {
	
		/* For debugging only */
		e match {
			// case _: ast.Literal =>
			// case _: Variable =>
			// case _: VariableExpr =>
			// case ThisExpr() =>
			case _ =>
				logger.debug("\nEVALUATING " + e)
				logger.debug(stateFormatter.format(σ))
		}
	
		e match {
			case _ =>
			logger.debug("Evaluating " + e)
			Success()
			
			// case Old(e0) =>
				// eval(σ \ (h = σ.g), cs, e0, m, c, Q)

			// case lit: ast.Literal => Q(evall(lit), c)

			// case v: Variable => Q(σ.γ(v), c)
			// case v: VariableExpr => Q(σ.γ(v.asVariable), c)
			// case ThisExpr() => Q(σ.γ(This), c)

			// /* ArithmeticExpr */
			// case ast.Plus(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Plus.apply, m, c, Q)
			// case ast.Minus(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Minus.apply, m, c, Q)
			// case ast.Times(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Times.apply, m, c, Q)
			
			// /* TODO: Assert that denominator is not zero. */
			// case ast.Div(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Div, m, c, Q)
			// case ast.Mod(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Mod, m, c, Q)

			// case ast.Not(e0) =>
				// eval(σ, cs, e0, m, c, (t, c1) =>
					// Q(terms.Not(t), c1))

			// case ast.And(e0, e1) if config.strictConjunctionEvaluation =>
				// evalBinOp(σ, cs, e0, e1, terms.And.apply, m, c, Q)
					
			// case ast.And(e0, e1) =>
				// var πPre: Set[Term] = Set()
				// var πAux: Set[Term] = Set()

				// var t0: Term = terms.True().setSrcNode(e0)
				// var t1: Term = terms.True().setSrcNode(e1)
				
				// eval(σ, cs, e0, m, c, (_t0, c1) => {
					// t0 = _t0
					// πPre = decider.π
					
					// val r = 
						// assume(t0, c1, (c2: C) =>
							// eval(σ, cs, e1, m, c2, (_t1, c3) => {
								// t1 = _t1
								// πAux = decider.π -- (πPre + t0)
								// Success(c3)}))
				
					// r && {
						// val tAux = state.terms.utils.SetAnd(πAux)
						// assume(tAux, c1, (c2: C) =>
							// Q(terms.And(t0, t1), c))}})
					
			// case ast.Or(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Or.apply, m, c, Q)		
			// case ast.Iff(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Iff.apply, m, c, Q)
			
			// case ast.Implies(e0, e1) if config.branchOverPureConditionals =>
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// (	if (!decider.assert(¬(t0)))
							// assume(t0, c1, (c2: C) => 
								// eval(σ, cs, e1, m, c2 + ImplBranching(true, e0, t0), (t1, c3) =>
									// Q(terms.Implies(t0, t1), c3)))
						// else
							// Success(c1)
					// ) &&
					// ( if (!decider.assert(t0))
							// assume(¬(t0), c1, (c2: C) =>
								// Q(terms.True(), c2 + ImplBranching(false, e0, t0)))
						// else
							// Success(c1)))
			
			// case impl @ ast.Implies(e0, e1) =>
				// /* - Problem with Implies(e0, e1) is that simply evaluating e1 after e0
				 // *   fails if e0 establishes a precondition of e1
				 // * - Hence we have to assume e0 when evaluating e1, but revoke that
				 // *   assumption afterwards
				 // * - We also have to keep track of all path conditions that result from
				 // *   the evaluation of e0 and e1
				 // */
				// val πPre: Set[Term] = decider.π
					// /* Initial set of path conditions */
				// var πIf: Set[Term] = Set()
					// /* Path conditions assumed while evaluating the antecedent */
				// var πThen: Set[Term] = Set()
					// /* Path conditions assumed while evaluating the consequent */
				
				// var tEvaluatedIf: Term = terms.False()
					// /* The term the antecedent actually evaluates too. */
				// var tEvaluatedThen: Term = terms.True()
					// /* The term the consequent actually evaluates too. */
					
				// val r =
					// eval(σ, cs, e0, m, c, (t0, c1) => {
						// πIf = decider.π -- πPre
						// tEvaluatedIf = t0
						// assume(t0, c1, (c2: C) =>
							// eval(σ, cs, e1, m, c2, (t1, c3) => {
								// πThen = decider.π -- (πPre ++ πIf + tEvaluatedIf)
								// tEvaluatedThen = t1
								// Success(c3)}))})
				
				// r && {
					// /* The additional path conditions gained while evaluating the
					 // * antecedent can be assumed in any case.
					 // * If the antecedent holds, then the additional path conditions
					 // * related to the consequent can also be assumed.
					 // */
					
					// val tAuxIf = state.terms.utils.SetAnd(πIf)
					// val tAuxThen = state.terms.utils.SetAnd(πThen)
					// val tAuxImplies = terms.Implies(tEvaluatedIf, tAuxThen)
					// val tImplies = terms.Implies(tEvaluatedIf, tEvaluatedThen)
					
					// assume(Set(tAuxIf, tAuxImplies), c, (c1: C) =>
						// Q(tImplies, c1))
				// }
				
			// case IfThenElse(e0, e1, e2) if config.branchOverPureConditionals =>
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// ((if (!decider.assert(¬(t0)))
						// assume(t0, c1, (c2: C) =>
							// eval(σ, cs, e1, m, c2 + IfBranching(true, e0, t0), Q))
					// else
						// Success(c1))
							// &&
					// (if (!decider.assert(t0))
						// assume(¬(t0), c1, (c2: C) =>
							// eval(σ, cs, e2, m, c2 + IfBranching(false, e0, t0), Q))
					// else
						// Success(c1))))
				
			// case ite @ ast.IfThenElse(e0, e1, e2) =>
				// val πPre: Set[Term] = decider.π
				// var πIf: Set[Term] = πPre
				// var πThen: Set[Term] = πPre
				// var πElse: Set[Term] = πPre
				// var tActualIf: Term = terms.False()
				// var tActualThen: Term = terms.True()
				// var tActualElse: Term = terms.True()
				// var ifEvaluated = false
				// var thenEvaluated = false
				// var elseEvaluated = false
				
				// decider.prover.push()
				
				// /* TODO: Use branch(...) helper method here - if possible */
				// val r =
					// eval(σ, cs, e0, m, c, (t0, c1) => {
						// πIf = decider.π -- πPre
						// πThen = decider.π
						// πElse = decider.π
						// tActualIf = t0
						// ifEvaluated = true
						// ((if (!decider.assert(¬(t0))) {
							// val r1 =
								// assume(t0, c1, (c2: C) =>
									// eval(σ, cs, e1, m, c2, (t1, c3) => {
										// πThen = decider.π -- (πPre ++ πIf + t0)
										// tActualThen = t1
										// thenEvaluated = true
										// Success(c3)}))
							// r1}
						// else
							// Success(c1))
							// &&
						// (if (!decider.assert(t0)) {
							// val r1 =
								// assume(¬(t0), c1, (c2: C) =>
									// eval(σ, cs, e2, m, c2, (t2, c3) => {
										// πElse = decider.π -- (πPre ++ πIf + ¬(t0))
										// tActualElse = t2
										// elseEvaluated = true
										// Success(c3)}))
							// r1}
						// else 
							// Success(c1)))})
				
				// decider.prover.pop()
				
				// r && {
					// val tIf: Term =
						// if (ifEvaluated) state.terms.utils.SetAnd(πIf) else terms.True()
					// val tThen: Term =
						// if (thenEvaluated) state.terms.utils.SetAnd(πThen) else terms.True()
					// val tElse: Term =
						// if (elseEvaluated) state.terms.utils.SetAnd(πElse) else terms.True()

					// /* Resolve problem that Ite(_, e1, e2) is not correctly typed if either
					 // * e1 or e2 (but not both) have not been evaluated because that branch
					 // * let to an inconsistent state detected by the smoke checker.
					 // */
					// if (!thenEvaluated && !elseEvaluated) {
						// logger.debug("[Evaluator] Evaluation of %s resulted in both branches being inconsistent.".format(ite))
						// Success(c)
					// } else {
						// if (!thenEvaluated) {
							// tActualThen = tActualThen.convert(tActualElse.sort)
						// } else if (!elseEvaluated) {
							// tActualElse = tActualElse.convert(tActualThen.sort)
						// }

						// val tIte = terms.Ite(tActualIf, tThen, tElse)
						// val tActualIte = terms.Ite(tActualIf, tActualThen, tActualElse)
						
						// assume(tIf, c, (c1: C) =>
							// assume(tIte, c1, (c2: C) =>
								// Q(tActualIte, c2)))
					// }
				// }

			// case ast.Less(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Less, m, c, Q)
			// case ast.AtMost(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.AtMost, m, c, Q)
			// case ast.AtLeast(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.AtLeast, m, c, Q)
			// case ast.Greater(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Greater, m, c, Q)
			
			// case eq: ast.EqExpr if eq.p0 == eq.p1 =>
				// /* Covers, amongst others, the probably very seldomly occuring 
				 // * comparison 'waitlevel == waitlevel'.
				 // */
				// Q(terms.True(), c)
				
			// case eq @ ast.Eq(e0, e1) =>
				// assert(e0.typ != null, /* @elidable */
						// "Expected ast.Eq(e0, _), e0.typ to be non-null: " + eq)
				// assert(e1.typ != null, /* @elidable */
						// "Expected ast.Eq(_, e1), e1.typ to be non-null: " + eq)			
				// // /* Fails when comparing nil<int> == [] */
				// // assert((   e0.typ == e1.typ
								// // || e0.typ.typ == ast.NullClass
								// // || e1.typ.typ == ast.NullClass), /* @elidable */
						// // "%s is not well-typed: %s != %s".format(eq, e0.typ, e1.typ))
				// assert(e0.typ.typ != null, /* @elidable */
						// "Expected ast.Eq(e0, _). e0.typ.typ to be non-null: " + e0.typ)

				// /* TODO: Have a case class SeqEq and let the ASTConverter convert
				 // *       Eqs on sequences to SeqEqs.
				 // *       This will clean up the evaluator.
				 // */
				// e0.typ.typ match {
					// case ast.SeqClass =>
						// evalBinOp(σ, cs, e0, e1, terms.SeqEq, m, c, Q)

					// case _ =>
						// /* Int, Bool, Ref, Mu (excluding waitlevel) */
						// evalBinOp(σ, cs, e0, e1, terms.TermEq, m, c, Q)
				// }
			
			// case FieldAccess(e0, id) =>
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ terms.Null()))
						// withFieldChunk(σ.h, t0, id, e0, m at e, c1, fc =>
							// Q(fc.value, c1))
					// else
						// Failure(m at e dueTo ReceiverMightBeNull(e0, id), c1))
			
			// case fapp @ FunctionApplication(e0, id, args) =>
				// val err = InvocationFailed(fapp) at fapp
				// val Result = specialVariables.result(fapp.f.out)
				
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// evals2(σ, args, Nil, m, c1, (tArgs, c2) => {
						// if (decider.assert(t0 ≠ Null())) {
							// assert(fapp.f != null, /* @elidable */
									// "Expected FunctionApplication.f to not be zero.")
							// assert(fapp.f.ins != null, /* @elidable */
									// "Expected FunctionApplication.f.ins to not be zero.")
							// bookkeeper.functionApplications += 1
							// val insΓ = Γ(((This, t0) :: fapp.f.ins.zip(tArgs)).toMap)							
							// val σ2 = σ \ insΓ
							// consume(σ2, Full, fapp.f.pre, err, c2, (_, s, c3) => {
								// val tFA = terms.FApp(fapp.f, s, t0, tArgs, toSort(fapp.f.out))
								
								// if (fappCache.contains(tFA)) {
									// logger.debug("[Eval(FApp)] Took cache entry for " + fapp)
									// val piFB = fappCache(tFA)
									// assume(piFB, c3, (c4: C) =>
										// Q(tFA, c4))}
								// else {
									// val σ3 = σ2 \+ (Result, tFA)
									// /* Break recursive cycles */
									// /* TODO: Replace cs by a multiset to have O(1) access */
									// if (cs.count(_ == fapp.f) < config.unrollFunctions) {
										// val πPre = decider.π
										// if (fapp.f.parent.module == thisClass.module) {
												// bookkeeper.functionBodyEvaluations += 1
												
												// eval(σ3, fapp.f :: cs, fapp.f.body, m, c3, (tFB, c4) =>
													// eval(σ3, fapp.f :: cs, fapp.f.post, m, c4, (tPost, c5) => {
														// val tFAEqFB = tFA ≡ tFB
														// if (config.cacheFunctionApplications)
															// fappCache += (tFA -> (decider.π -- πPre + tFAEqFB + tPost))
														// assume(Set(tFAEqFB, tPost), c5, (c6: C) =>
															// Q(tFA, c6))}))}
										// else {
											// /* Function body is invisible, use postcondition instead */
											// eval(σ3, fapp.f :: cs, fapp.f.post, m, c3, (tPost, c4) => {
												// if (config.cacheFunctionApplications)
													// fappCache += (tFA -> (decider.π -- πPre + tPost))
												// assume(tPost, c4, (c5: C) =>
														// Q(tFA, c5))})}}
									// else
										// Q(tFA, c3)}})}
						// else
							// Failure(err dueTo ReceiverMightBeNull(e0, id), c2)}))

			// case Unfolding(acc @ Access(pa @ PredicateAccess(e0, id), p0), e1) =>
				// assert(pa.p != null, /* @elidable */
					// "Expected Access.ma to not be null")
				// val err = UnfoldingFailed
				// evalp(σ, p0, m, c, (pt, c1) =>
					// if (decider.isNonNegativeFraction(pt))
						// eval(σ, cs, e0, err, c1, (t0, c2) =>
							// /* TODO: t0 non-null check */
							// consume(σ, Full, acc, err, c2, (σ1, snap, c3) => {
								// val insΓ = Γ((This -> t0))
									// /* Unfolding only effects the current heap */
									// produce(σ1 \ insΓ, snap, pt, pa.p.body, err, c3, (σ2, c4) => {
										// val σ3 = σ2 \ (g = σ.g, γ = σ.γ)
										// eval(σ3, cs, e1, err, c4, Q)})}))
					// else
						// Failure(FractionMightBeNegative at e withDetails (e0, id), c1))

			// /*
			 // * Quantifications
			 // */
		
			// /* TODO: If the quantification contains a sequence access, e.g. xs[i].x,
			 // *       we must have at least rd(xs[*].x) access.
			 // */
			// case sq @ SeqQuantification(q, ids, seq, body) =>
				// seq match {
					// case _: EmptySeq => Q(terms.True(), c)

					// /* Evaluates Chalice in-quantifications to Syxc quantifications:
					 // *  -    forall i1,...,ir in xs :: P
					 // *    	 -> forall t1,...,tr :: t1 in ts && ... && tr in ts => P
					 // *  -    exists i1,...,ir in xs :: P
					 // *    	 -> exists t1,...,tr :: t1 in ts && ... && tr in ts && P
					 // */
					// case _ =>
						// val guard = ast.utils.collections.SetAnd(
							// sq.vars map (v => new VariableExpr(v)),
							// ve => ast.SeqIn(seq, ve))
						// val quantOp = q match {
							// case ast.Forall() => ast.Implies.apply _
							// case ast.Exists() => ast.And.apply _}
						// val tq =
							// TypeQuantification(q, ids, IntType(), quantOp(guard, body))
						// tq.vars = sq.vars
						// eval(σ, cs, tq, m, c, Q)}
				
			// case tq @ TypeQuantification(q, ids, t, body) =>
				// assert(ids.length == tq.vars.length, "TypeQuantification seems to be inconsistent w.r.t. the number of quantified variables")
				
				// /* Evaluates Chalice type-quantifications to Syxc quantifications:
				 // *  -    forall x1,...,xr: T :: P  ->  forall x1,...,xr: T :: P
				 // *  -    exists x1,...,xr: T :: P  ->  exists x1,...,xr: T :: P
				 // */
				// val tVars: List[terms.Var] = tq.vars map fresh _
				// val idsΓ = Γ(tq.vars.zip(tVars).toMap)
				
				// val tQuantOp = q match {
					// case ast.Forall() => terms.Forall
					// case ast.Exists() => terms.Exists}
					
				// val tRelGuardBody = q match {
					// case ast.Forall() => terms.Implies.apply _
					// case ast.Exists() => terms.And.apply _}

				// /* Why so cumbersome? Why not simply eval(..., tBody => Q(..., tBody))?
				 // *  - Assume we have a quantification forall x: int :: x > 0 ==> f(x) > 0
				 // *  - Evaluating the body yields a term Implies(lhs, rhs) which will be
				 // *    used as the body if the Quantification term
				 // *  - The evaluation also yields additional path conditions, for example
				 // *    the relation between the function application and the evaluated
				 // *    function body, e.g. f(x) == 2x
				 // *  - These are not returned but added to the path conditions during they
				 // *    evaluation of the function application
				 // *  - However, we need them to occur inside the quantification, not
				 // *    outside of it, because assumptions outside of the quantification
				 // *    will not be considered even if the quantified variable occurs in
				 // *    them due to the scope of the quantified variables
				 // *  - We thus have to determine these additional path conditions
				 // *    to be able to include them in the quantification
				 // *
				 // * ATTENTION The current implementation unfortunately disallows branching
				 // * evaluations!
				 // * Consider e.g. e0 ==> e1 which could be evaluated by
				 // * branching over e0, returning once t0 ==> t1 and once ¬t0 ==> true.
				 // * However, the second branch's result overwrites the first branch's
				 // * result when being assigned to tActualBody. Hence, only the second
				 // * branch is asserted which always succeeds.
				 // *
				 // * A possible solution would be to make tActualBody and πPost lists and
				 // * to eventually invoke Q with a list of conjuncted quantifications.
				 // */
				
				// val πPre: Set[Term] = decider.π
				// var πPost: Set[Term] = πPre
				// var tActualBody: Term = terms.True()
				
				// decider.prover.push()
				
				// val r =
					// eval(σ \+ idsΓ, cs, body, m, c, (tBody, c1) => {
						// tActualBody = tBody
						// πPost = decider.π
						// /* We could call Q directly instead of returning Success, but in
						 // * that case the path conditions πDelta would also be outside of
						 // * the quantification. Since they are not needed outside of the
						 // * quantification we go the extra mile to get ride of them in order
						 // * to not pollute the path conditions.
						 // *
						 // * Actually, only path conditions in which the quantified variable
						 // * occurrs are waste, others, especially $combine-terms, are actually
						 // * of interest and should be in the path conditions to avoid the
						 // * 'fapp-requires-separating-conjunction-fresh-snapshots' problem,
						 // * which is currently overcome by caching fapp-terms.
						 // */
						// Success(c1)})

				// decider.prover.pop()
						
				// r && {
					// val πDelta = πPost -- πPre
					// val tAux = state.terms.utils.SetAnd(πDelta)
					// val tQuantAux = terms.Quantification(tQuantOp, tVars, tAux)
					// val tQuant = terms.Quantification(tQuantOp, tVars, tActualBody)

					// assume(tQuantAux, c, (c1: C) =>
						// Q(tQuant, c1))}
						
			// /*
			 // * Sequences
			 // */			
			
			// case ExplicitSeq(es) =>
				// import terms.{SeqTerm, SeqElem, SeqCon, SeqLen, IntLiteral}
				
				// evals2(σ, es.reverse, Nil, m, c, (tEs, c1) => {
					// val tSeq =
						// tEs.tail.foldLeft[SeqTerm](SeqElem(tEs.head))((tSeq, te) =>
							// SeqCon(SeqElem(te), tSeq))
					// assume(SeqLen(tSeq) ≡ IntLiteral(es.size), c1, (c2: C) =>
						// Q(tSeq, c2))})
					
			// case RangeSeq(min, max) =>
				// evalBinOp(σ, cs, min, max, terms.RangeSeq, m, c, Q)
			
			// case SeqLength(e0) =>
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// Q(terms.SeqLen(t0), c1))
					
			// case SeqCon(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.SeqCon, m, c, Q)
			
			// case SeqAt(e0, e1) =>
				// /* TODO: Implement boundary checks: t1 >= 0 && t1 < |t0| */
				// evalBinOp(σ, cs, e0, e1, terms.SeqAt, m, c, Q)
					
			// case SeqDrop(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.SeqDrop, m, c, Q)
			// case SeqTake(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.SeqTake, m, c, Q)
			
			// case SeqIn(e0, e1) => e0 match {
				// case RangeSeq(eMin, eMax) =>
					// eval(σ, cs, eMin, m, c, (tMin, c1) =>
						// eval(σ, cs, eMax, m, c1, (tMax, c2) =>
							// eval(σ, cs, e1, m, c2, (t1, c3) => {
								// val tRange =
									// terms.And(terms.AtMost(tMin, t1), terms.Less(t1, tMax))
								// Q(tRange, c3)})))
					
				// // case ExplicitSeq(es) => /* TODO: e1 == es1 OR ... OR e1 == esn */
				// case _ => evalBinOp(σ, cs, e0, e1, terms.SeqIn, m, c, Q)}

			// /*
			 // * Locks
			 // */

			// case ast.Holds(e0, p0) =>
				// eval(σ, cs, e0, m, c, (t0, c1) =>
					// Q(lockSupport.Holds(σ.h, t0, evallm(p0)), c1))
			
			// case ast.MaxLockAtMost(_, eMu) =>
				// if (config.disableDeadlockChecks)
					// Q(terms.True(), c)
				// else
					// eval(σ, cs, eMu, m, c, (tMu, c1) =>
						// Q(lockSupport.MaxLockAtMost(σ.h, tMu), c1))

			// case ast.MaxLockLess(_, eMu) =>
				// if (config.disableDeadlockChecks)
					// Q(terms.True(), c)
				// else
					// eval(σ, cs, eMu, m, c, (tMu, c1) =>
						// Q(lockSupport.MaxLockLess(σ.h, tMu), c1))

			// case ast.LockLess(e0, e1) =>
				// if (config.disableDeadlockChecks)
					// Q(terms.True(), c)
				// else
					// evalBinOp(σ, cs, e0, e1, terms.LockLess, m, c, Q)
					
			// case ast.LockChangeExpr(ast.LockChange(es)) =>
				// if (config.disableDeadlockChecks)
					// Q(terms.True(), c)
				// else
					// evals(σ, es, m, c, (ts, c1) =>
						// Q(lockSupport.LockChange(σ.h, σ.g, ts), c1))
				
			// /*
			 // * Credits
			 // */
			 
			// case ast.Credits(e0, e1) =>
				// val f = (t0: Term, t1: Term) =>
					// terms.AtLeast(creditSupport.Credits(σ.h, t0), t1)
				// evalBinOp(σ, cs, e0, e1, f, m, c, Q)
						
			// case ast.DebtFreeExpr() =>
				// Q(creditSupport.DebtFreeExpr(σ.h), c)
		}
	}

	private def evalBinOp[T <: Term](σ: S, cs: List[SILFunction],
			e0: SILExpression, e1: SILExpression, termOp: (Term, Term) => T, m: Message,
			Q: Term => VerificationResult): VerificationResult =

		eval(σ, cs, e0, m, t0 =>
			eval(σ, cs, e1, m, t1 =>
				Q(termOp(t0, t1))))

	override def pushLocalState() {
		fappCacheFrames = fappCacheFrames.push(fappCache)
		super.pushLocalState()
	}
	
	override def popLocalState() {
		fappCache = fappCacheFrames.top
		fappCacheFrames = fappCacheFrames.pop
		super.popLocalState()
	}
}