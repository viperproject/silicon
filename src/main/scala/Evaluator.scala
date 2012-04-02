package ch.ethz.inf.pm.silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging

import silAST.expressions.{Expression => SILExpression}
    // PermissionExpression => SILPermissionExpression,
    // PBinaryExpression => SILPBinaryExpression,
    // TrueExpression => SILTrue,
    // FalseExpression => SILFalse,
    // DomainPredicateExpression => SILDomainPredicateExpression}
    // BinaryExpression => SILBinaryExpression}
import silAST.programs.symbols.{
    Function => SILFunction,
    ProgramVariable => SILProgramVariable}
import silAST.expressions.terms.{LiteralTerm => SILLiteral}
import silAST.expressions.terms.{Term => SILTerm}

import interfaces.{Evaluator, Consumer, Producer, VerificationResult,
		Failure, Success}
import interfaces.state.{Store, Heap, PathConditions, State, 
		StateFormatter, StateFactory, HeapMerger}
import interfaces.decider.Decider
import interfaces.reporting.{Message}
// import interfaces.ast.specialVariables
// import interfaces.ast.specialVariables.This
import interfaces.state.FieldChunk
import interfaces.state.factoryUtils.Ø
/*
import ast.{Expression, Variable, FieldAccess, Old, ArithmeticExpr,
		CompareExpr, BooleanExpr, VariableExpr, ThisExpr, FunctionApplication, 
		IfThenElse, Unfolding, Access, PredicateAccess, SeqQuantification, RangeSeq,
		ExplicitSeq, EmptySeq, SeqLength, SeqCon, SeqAt, SeqIn, SeqTake, SeqDrop,
		TypeQuantification, IntType}
*/
import state.{TypeConverter /* , CounterChunk */}
import state.terms
import state.terms.{Term, Null, PermissionTerm}
import reporting.ErrorMessages.{InvocationFailed, UnfoldingFailed, 
		FractionMightBeNegative}
import reporting.Reasons.{ReceiverMightBeNull, InsufficientPermissions}
import reporting.{/* Evaluating, IfBranching, ImplBranching, */ Bookkeeper}
import reporting.utils._
import state.terms.utils.¬

trait DefaultEvaluator[ST <: Store[SILProgramVariable, ST],
                       H <: Heap[H],
											 PC <: PathConditions[PC],
                       S <: State[SILProgramVariable, ST, H, S]]
		extends Evaluator[SILProgramVariable, SILExpression, SILTerm, ST, H, S]
		with    HasLocalState
		{ this:      Logging
            with Consumer[SILProgramVariable, SILExpression, ST, H, S]
            with Producer[SILProgramVariable, SILExpression, ST, H, S] =>

	protected val decider: Decider[SILProgramVariable, ST, H, PC, S]
	import decider.{fresh, assume}
										
	protected val stateFactory: StateFactory[SILProgramVariable, ST, H, S]
	import stateFactory._
	
	// protected val permissionFactory: PermissionFactory[P]
	// import permissionFactory._
	
	//protected val lockSupport: LockSupport[ST, H, S]
	//protected val creditSupport: CreditSupport[ST, H, S]
	
	protected val typeConverter: TypeConverter
	import typeConverter.toSort
	
	protected val chunkFinder: ChunkFinder[H]
	import chunkFinder.withFieldChunk
	
	protected val stateFormatter: StateFormatter[SILProgramVariable, ST, H, S, String]

	protected val config: Config
	protected val bookkeeper: Bookkeeper
	
	// protected var thisClass: ast.Class
	
	private var fappCache: Map[Term, Set[Term]] = Map()
	private var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()
	
	def evales(σ: S, es: Seq[SILExpression], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult =

		evales2(σ, es, Nil, m, ts =>
			Q(ts))
			
	def evale(σ: S, e: SILExpression, m: Message, Q: Term => VerificationResult)
           : VerificationResult =
			
		evale(σ, Nil, e, m, t =>
			Q(t))
      
	def evalts(σ: S, es: Seq[SILTerm], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult =

		evalts2(σ, es, Nil, m, ts =>
			Q(ts))
      
	def evalt(σ: S, e: SILTerm, m: Message, Q: Term => VerificationResult)
          : VerificationResult =

		evalt(σ, List[SILFunction](), e, m, t =>
			Q(t))

	def evalp(σ: S, p: SILTerm, m: Message, Q: PermissionTerm => VerificationResult) =
    p match {
      case silAST.expressions.terms.FullPermissionTerm() => Q(terms.FullPerms())
      case silAST.expressions.terms.NoPermissionTerm() => Q(terms.ZeroPerms())
      case silAST.expressions.terms.EpsilonPermissionTerm() => Q(terms.EpsPerms())
      case silAST.expressions.terms.ProgramVariableTerm(v) => Q(terms.Perms(σ.γ(v)))
      
      case _ =>
        evalt(σ, p, m, tp =>
          Q(terms.Perms(tp)))
    }

    // p match {
			
		// case ast.ConstFraction(per, eps) =>
			// Q(state.ConstFraction(per, eps))

		// case ast.ExprFraction(per, eps) =>
			// eval(σ, Nil, per, m, tPer =>
				// eval(σ, Nil, eps, m, tEps =>
					// Q(state.TermFraction(tPer, tEps))))
	// }
			
	private def evales2(σ: S, es: Seq[SILExpression], ts: List[Term], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult = {

		if (es.isEmpty)
			Q(ts.reverse)
		else
			evale(σ, Nil, es.head, m, t =>
				evales2(σ, es.tail, t :: ts, m, Q))
	}
  
	private def evalts2(σ: S, es: Seq[SILTerm], ts: List[Term], m: Message,
			Q: List[Term] => VerificationResult): VerificationResult = {

		if (es.isEmpty)
			Q(ts.reverse)
		else
			evalt(σ, Nil, es.head, m, t =>
				evalts2(σ, es.tail, t :: ts, m, Q))
	}
	
	// def evall(lit: SILLiteral): Term = lit match {
		// case _ =>
			// logger.debug("Evaluating literal " + lit)
			// null
		// // case ast.Null() => terms.Null()
		// // case ast.True() => terms.True()
		// // case ast.False() => terms.False()
		// // case ast.IntLiteral(n) => terms.IntLiteral(n)
		// // // case ast.MaxLock() => terms.MaxLock
		// // case ast.BottomLock() => terms.BottomLock()
		// // case ast.EmptySeq(_) => terms.EmptySeq()
		// // case ast.FreshLiteral => fresh
			// // /* TODO: Parameterise FreshLiteral with expected type */
	// }
	
	// def evallm(lm: ast.LockMode): terms.LockMode = lm match {
		// case ast.ReadLockMode => terms.LockMode.Read
		// case ast.WriteLockMode => terms.LockMode.Write
	// }
	
	protected def evale(σ: S, cs: List[SILFunction], e: SILExpression, m: Message, 
			Q: Term => VerificationResult): VerificationResult =
			
		evale2(σ, cs, e, m, t => {
			t.setSrcNode(e)
			Q(t)})
      
	protected def evalt(σ: S, cs: List[SILFunction], e: SILTerm, m: Message,
                      Q: Term => VerificationResult)
                     : VerificationResult =

		evalt2(σ, cs, e, m, t => {
			t.setSrcNode(e)
			Q(t)})
	
	/* Attention: Only use eval(σ, cs, e, m, c Q) inside of eval2, because
	 *   - eval adds an "Evaluating" operation to the context
	 *   - eval sets the source node of the resulting term
	 */
	protected def evale2(σ: S, cs: List[SILFunction], e: SILExpression, m: Message, 
			Q: Term => VerificationResult): VerificationResult = {
	
		// /* For debugging only */
		// e match {
			// // case _: ast.Literal =>
			// // case _: Variable =>
			// // case _: VariableExpr =>
			// // case ThisExpr() =>
			// case _ =>
				// logger.debug("\nEVALUATING EXPRESSION " + e)
				// logger.debug("  " + e.getClass.getName)
				// logger.debug(stateFormatter.format(σ))
		// }
	
		e match {
			// case _ =>
			// // logger.debug("Evaluating expression " + e)
			// Success()
      
      case silAST.expressions.TrueExpression() => Q(terms.True())
      case silAST.expressions.FalseExpression() => Q(terms.False())

			// case Old(e0) =>
				// eval(σ \ (h = σ.g), cs, e0, m, c, Q)

			// case lit: ast.Literal => Q(evall(lit), c)

			// case v: Variable => Q(σ.γ(v), c)
			// case v: VariableExpr => Q(σ.γ(v.asVariable), c)
			// case ThisExpr() => Q(σ.γ(This), c)
      
      case silAST.expressions.UnaryExpression(op, e0) =>
        // logger.debug("  op = " + op + ", " + op.getClass.getName)
        // logger.debug("  e0 = " + e0 + ", " + e0.getClass.getName)
        
        op match {
          case silAST.symbols.logical.Not() =>
            evale(σ, cs, e0, m, t0 =>
              Q(terms.Not(t0)))
        }
      
      case silAST.expressions.BinaryExpression(op, e0, e1) =>
        // logger.debug("  op = " + op + ", " + op.getClass.getName)
        // logger.debug("  e0 = " + e0 + ", " + e0.getClass.getName)
        // logger.debug("  e1 = " + e1 + ", " + e1.getClass.getName)

        op match {
          case silAST.symbols.logical.And() if config.strictConjunctionEvaluation =>
              evalBinOp(σ, cs, e0, e1, terms.And, m, Q)

          case silAST.symbols.logical.And() =>            
            var πPre: Set[Term] = Set()
            var πAux: Set[Term] = Set()

            var t0: Term = terms.True().setSrcNode(e0)
            var t1: Term = terms.True().setSrcNode(e1)

            evale(σ, cs, e0, m, _t0 => {
              t0 = _t0
              πPre = decider.π
              
              val r = 
                assume(t0,
                  evale(σ, cs, e1, m, _t1 => {
                    t1 = _t1
                    πAux = decider.π -- (πPre + t0)
                    Success()}))
            
              r && {
                val tAux = state.terms.utils.BigAnd(πAux)
                assume(tAux,
                  Q(terms.And(t0, t1)))}})
            
          case silAST.symbols.logical.Implication()
               if config.branchOverPureConditionals =>

            evale(σ, cs, e0, m, t0 =>
              (	if (!decider.assert(¬(t0)))
                  assume(t0,
                    evale(σ, cs, e1, m, t1 =>
                      Q(terms.Implies(t0, t1))))
                else
                  Success()
              ) &&
              ( if (!decider.assert(t0))
                  assume(¬(t0),
                    Q(terms.True()))
                else
                  Success()))
          
          case silAST.symbols.logical.Implication() =>
            /* - Problem with Implies(e0, e1) is that simply evaluating e1 after e0
             *   fails if e0 establishes a precondition of e1
             * - Hence we have to assume e0 when evaluating e1, but revoke that
             *   assumption afterwards
             * - We also have to keep track of all path conditions that result from
             *   the evaluation of e0 and e1
             */
            val πPre: Set[Term] = decider.π
              /* Initial set of path conditions */
            var πIf: Set[Term] = Set()
              /* Path conditions assumed while evaluating the antecedent */
            var πThen: Set[Term] = Set()
              /* Path conditions assumed while evaluating the consequent */
            
            var tEvaluatedIf: Term = terms.False()
              /* The term the antecedent actually evaluates too. */
            var tEvaluatedThen: Term = terms.True()
              /* The term the consequent actually evaluates too. */
              
            val r =
              evale(σ, cs, e0, m, t0 => {
                πIf = decider.π -- πPre
                tEvaluatedIf = t0
                assume(t0,
                  evale(σ, cs, e1, m, t1 => {
                    πThen = decider.π -- (πPre ++ πIf + tEvaluatedIf)
                    tEvaluatedThen = t1
                    Success()}))})
            
            r && {
              /* The additional path conditions gained while evaluating the
               * antecedent can be assumed in any case.
               * If the antecedent holds, then the additional path conditions
               * related to the consequent can also be assumed.
               */
              
              val tAuxIf = state.terms.utils.BigAnd(πIf)
              val tAuxThen = state.terms.utils.BigAnd(πThen)
              val tAuxImplies = terms.Implies(tEvaluatedIf, tAuxThen)
              val tImplies = terms.Implies(tEvaluatedIf, tEvaluatedThen)
              
              assume(Set(tAuxIf, tAuxImplies),
                Q(tImplies))
            }
            
          case silAST.symbols.logical.Or() =>
            evalBinOp(σ, cs, e0, e1, terms.Or, m, Q)
      }

      case eq: silAST.expressions.EqualityExpression =>
        evalBinOp(σ, cs, eq.term1, eq.term2, terms.Eq, m, Q)
        
      case silAST.expressions.QuantifierExpression(quant, qvar, body) =>
			// case tq @ TypeQuantification(q, ids, t, body) =>

				// val tVars: List[terms.Var] = tq.vars map fresh _
				// val idsΓ = Γ(tq.vars.zip(tVars).toMap)
				
				val tQuantOp = quant match {
					case silAST.symbols.logical.quantification.Forall() => terms.Forall
					case silAST.symbols.logical.quantification.Exists() => terms.Exists
        }
					
				// val tRelGuardBody = q match {
					// case ast.Forall() => terms.Implies.apply _
					// case ast.Exists() => terms.And.apply _}

				/* Why so cumbersome? Why not simply eval(..., tBody => Q(..., tBody))?
				 *  - Assume we have a quantification forall x: int :: x > 0 ==> f(x) > 0
				 *  - Evaluating the body yields a term Implies(lhs, rhs) which will be
				 *    used as the body of the Quantification term
				 *  - The evaluation also yields additional path conditions, for example
				 *    the relation between the function application and the evaluated
				 *    function body, e.g. f(x) == 2x
				 *  - These are not returned but added to the path conditions during they
				 *    evaluation of the function application
				 *  - However, we need them to occur inside the quantification, not
				 *    outside of it, because assumptions outside of the quantification
				 *    will not be considered even if the quantified variable occurs in
				 *    them due to the scope of the quantified variables
				 *  - We thus have to compute these additional path conditions
				 *    to be able to include them in the quantification
				 *
				 * ATTENTION The current implementation unfortunately disallows branching
				 * evaluations!
				 * Consider e.g. e0 ==> a1 which could be evaluated by
				 * branching over e0 if a1 is not pure, executing one branch with t0
         * and one with ¬t0.
				 * However, the second branch's result overwrites the first branch's
				 * result when being assigned to tActualBody. Hence, only the second
				 * branch is asserted which always succeeds.
				 *
				 * A possible solution would be to make tActualBody and πPost lists and
				 * to eventually invoke Q with a list of conjuncted quantifications.
				 */
				
				val πPre: Set[Term] = decider.π
				var πPost: Set[Term] = πPre
				var tActualBody: Term = terms.True()
				
				decider.prover.push()
        decider.prover.logComment("Evaluating " + e)
				
        val pv = ast.utils.lv2pv(qvar)
        val tPv = fresh(pv)
        
				val r =
					evale(σ \+ (pv, tPv), cs, body, m, tBody => {
						tActualBody = tBody
						πPost = decider.π
						/* We could call Q directly instead of returning Success, but in
						 * that case the path conditions πDelta would also be outside of
						 * the quantification. Since they are not needed outside of the
						 * quantification we go the extra mile to get rid of them in order
						 * to not pollute the path conditions.
						 *
						 * Actually, only path conditions in which the quantified variable
						 * occurrs are waste, others, especially $combine-terms, could be
						 * relevant and should be in the path conditions to avoid the
						 * 'fapp-requires-separating-conjunction-fresh-snapshots' problem,
						 * which is currently overcome by caching fapp-terms.
						 */
						Success()})

				decider.prover.pop()
						
				r && {
					val πDelta = πPost -- πPre
					val tAux = state.terms.utils.BigAnd(πDelta)
					val tQuantAux = terms.Quantification(tQuantOp, tPv, tAux)
					val tQuant = terms.Quantification(tQuantOp, tPv, tActualBody)

					assume(tQuantAux,
						Q(tQuant))}

      case silAST.expressions.DomainPredicateExpression(predicate, args) =>
        // logger.debug("  predicate = " + predicate + ", " + predicate.getClass.getName)
        // logger.debug("  args = " + args + ", " + args.getClass.getName)

        predicate match {
          /* PermissionTerm */
          
          case silAST.types.permissionEQ =>
            evalBinOp(σ, cs, args(0), args(1), terms.Eq, m, Q)

          case silAST.types.permissionNE =>
            val neq = (t1: Term, t2: Term) => t1 ≠ t2
            evalBinOp(σ, cs, args(0), args(1), neq, m, Q)

          case silAST.types.permissionLE =>
            evalBinOp(σ, cs, args(0), args(1), terms.AtMost, m, Q)

          case silAST.types.permissionLT =>
            evalBinOp(σ, cs, args(0), args(1), terms.Less, m, Q)

          case silAST.types.permissionGE =>
            evalBinOp(σ, cs, args(0), args(1), terms.AtLeast, m, Q)

          case silAST.types.permissionGT =>
            evalBinOp(σ, cs, args(0), args(1), terms.Greater, m, Q)

          /* Integers */

          case silAST.types.integerEQ =>
            evalBinOp(σ, cs, args(0), args(1), terms.Eq, m, Q)

          case silAST.types.integerNE =>
            val neq = (t1: Term, t2: Term) => t1 ≠ t2
            evalBinOp(σ, cs, args(0), args(1), neq, m, Q)

          case silAST.types.integerLE =>
            evalBinOp(σ, cs, args(0), args(1), terms.AtMost, m, Q)

          case silAST.types.integerLT =>
            evalBinOp(σ, cs, args(0), args(1), terms.Less, m, Q)

          case silAST.types.integerGE =>
            evalBinOp(σ, cs, args(0), args(1), terms.AtLeast, m, Q)

          case silAST.types.integerGT =>
            evalBinOp(σ, cs, args(0), args(1), terms.Greater, m, Q)

          /* Booleans */

          case silAST.types.booleanEvaluate =>
            evalt(σ, cs, args(0), m, Q)

          /* Domains not directly handled */
            
          case dp: silAST.domains.DomainPredicate =>
                   // if dp.name == "EvalBool[Boolean[]]" =>
            
            // assert(dp.signature.parameterTypes.length == 1, "Expected one argument to %s (%s), but found %s: %s".format(dp, dp.getClass.getName, dp.signature.parameterTypes.length, dp.signature.parameterTypes))
            
            // logger.debug("[evale2/DomainPredicateExpression/DomainPredicate]")
            // logger.debug("  dp = " + dp)
            // logger.debug("  dp.name = " + dp.name)
            // logger.debug("  dp.signature.parameterTypes = " + dp.signature.parameterTypes)
            
            evalts(σ, args, m, tArgs =>
              Q(terms.DomainFApp(dp.fullName, tArgs, terms.sorts.Bool)))
            
            // Q(terms.True())
            // sys.error("")
            // evalBinOp(σ, cs, args.args(0), args.args(1), terms.AtLeast, m, Q)
        }

			// /* ArithmeticExpr */
			// case ast.Plus(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Plus.apply, m, c, Q)
			// case ast.Minus(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Minus.apply, m, c, Q)
			// case ast.Times(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Times.apply, m, c, Q)
			
			// /* TODO: Assert that denominator is not zero. */
			// case ast.Div(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Div, m, c, Q)
			// case ast.Mod(e0, e1) => evalBinOp(σ, cs, e0, e1, terms.Mod, m, c, Q)

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
  
	protected def evalt2(σ: S, cs: List[SILFunction], e: SILTerm, m: Message,
                       Q: Term => VerificationResult)
                     : VerificationResult = {

		// /* For debugging only */
		// e match {
			// // case _: ast.Literal =>
			// // case _: Variable =>
			// // case _: VariableExpr =>
			// // case ThisExpr() =>
			// case _ =>
				// logger.debug("\nEVALUATING TERM " + e)
				// logger.debug("  " + e.getClass.getName)
				// logger.debug("  " + e.sourceLocation)
				// logger.debug(stateFormatter.format(σ))
		// }
	
		e match {
      case ilt: silAST.expressions.terms.IntegerLiteralTerm =>
        Q(terms.IntLiteral(ilt.value.intValue))
      
			// case v: Variable => Q(σ.γ(v), c)
			// case v: VariableExpr => Q(σ.γ(v.asVariable), c)
      case silAST.expressions.terms.ProgramVariableTerm(v) => Q(σ.γ(v))
      case silAST.expressions.terms.LogicalVariableTerm(v) => Q(σ.γ(ast.utils.lv2pv(v)))
      
      case silAST.expressions.terms.PermTerm(rcvr, field) =>
        evalFieldDeref(σ, cs, rcvr, field, m, fc =>
          Q(fc.perm))
          
        // evalt(σ, cs, es(0), m, t0 =>
        // Q(terms.PermTerm())
      
      case silAST.expressions.terms.FieldReadTerm(rcvr, field) =>
        evalFieldDeref(σ, cs, rcvr, field, m, fc =>
          Q(fc.value))
				// evalt(σ, cs, rcvr, m, tRcvr =>
					// if (decider.assert(tRcvr ≠ Null()))
						// withFieldChunk(σ.h, tRcvr, field.name, rcvr.toString, m at rcvr, fc =>
							// Q(fc.value))
					// else
						// Failure(m at rcvr dueTo ReceiverMightBeNull(rcvr.toString, field.name)))
      
      case npt @ silAST.expressions.terms.NoPermissionTerm() =>
           // if npt.eq(silAST.expressions.terms.NoPermissionTerm) =>
        // logger.debug("[evalt2] " + e)
        // logger.debug("[evalt2] " + e.getClass.getName)
        // logger.debug("[evalt2] " + (e == silAST.expressions.terms.noPermissionTerm))
        // logger.debug("[evalt2] " + e.eq(silAST.expressions.terms.noPermissionTerm))
        Q(terms.ZeroPerms())
        
      case fpt @ silAST.expressions.terms.FullPermissionTerm() =>
           // if fpt.eq(silAST.expressions.terms.FullPermissionTerm) =>
        // logger.debug("[evalt2] " + e)
        // logger.debug("[evalt2] " + e.getClass.getName)
        // logger.debug("[evalt2] " + (e == silAST.expressions.terms.noPermissionTerm))
        // logger.debug("[evalt2] " + e.eq(silAST.expressions.terms.noPermissionTerm))
        Q(terms.FullPerms())

      case silAST.expressions.terms.DomainFunctionApplicationTerm(f, es) => f match {
        /* Booleans */        
        case silAST.types.booleanTrue => Q(terms.True())
        case silAST.types.booleanFalse => Q(terms.False())
        
        case silAST.types.booleanNegation =>
          evalt(σ, cs, es(0), m, t0 =>
            Q(terms.Not(t0)))
        
        /* TODO: Not short-circuiting, combine with AND above. */
        case silAST.types.booleanConjunction =>
          evalBinOp(σ, cs, es(0), es(1), terms.And, m, Q)
        
        case silAST.types.booleanDisjunction =>
          evalBinOp(σ, cs, es(0), es(1), terms.Or, m, Q)
        
        /* TODO: Not sufficient, combine with IMPLIES above. */
        case silAST.types.booleanImplication =>
          evalBinOp(σ, cs, es(0), es(1), terms.Implies, m, Q)
        
        case silAST.types.booleanEquivalence =>
          evalBinOp(σ, cs, es(0), es(1), terms.Iff, m, Q)
        
        /* References */
        
        case silAST.types.nullFunction => Q(terms.Null())
        
        case silAST.types.referenceEquality =>
          evalBinOp(σ, cs, es(0), es(1), terms.Eq, m, Q)
          
        /* Integers */
        
        case silAST.types.integerAddition =>
          evalBinOp(σ, cs, es(0), es(1), terms.Plus, m, Q)
        
        case silAST.types.integerSubtraction =>
          evalBinOp(σ, cs, es(0), es(1), terms.Minus, m, Q)
          
        case silAST.types.integerMultiplication =>
          evalBinOp(σ, cs, es(0), es(1), terms.Times, m, Q)
          
        case silAST.types.integerDivision =>
          evalBinOp(σ, cs, es(0), es(1), terms.Div, m, Q)
          
        case silAST.types.integerModulo =>
          evalBinOp(σ, cs, es(0), es(1), terms.Mod, m, Q)

        // case silAST.types.integerDivision => "(/ %s %s)".format(convert(ts(0)), convert(ts(1)))
        // case silAST.types.integerModulo => "(% %s %s)".format(convert(ts(0)), convert(ts(1)))
        // case silAST.types.integerNegation => "(- 0 %s)".format(convert(ts(0)))
        
        /* Permissions */
        
        case silAST.types.permissionAddition =>
          evalBinOp(σ, cs, es(0), es(1), terms.PermPlus, m, Q)
        
        case silAST.types.percentagePermission =>
          sys.error("Not yet implemented: " + e)
          
        case silAST.types.permissionSubtraction =>
          evalBinOp(σ, cs, es(0), es(1), terms.PermMinus, m, Q)
          
        case silAST.types.permissionMultiplication =>
          evalBinOp(σ, cs, es(0), es(1), terms.PermTimes, m, Q)
          
        case silAST.types.permissionIntegerMultiplication =>
          sys.error("Not yet implemented: " + e)
        
        /* Domains not handled directly */
        
        case _ =>
          evalts(σ, es, m, ts =>
            Q(terms.DomainFApp(f.fullName, ts, toSort(f.signature.resultType))))
      }
           // if f.name == "True" =>
           
        // Q(terms.True())
        // logger.debug("[evalt2/DomainFunctionApplicationTerm]")
        // logger.debug("  f = " + f)
        // logger.debug("  f.name = " + f.name)
        // logger.debug("  es = " + es)
        // logger.debug("  es.length = " + es.length)
        // sys.error("")
        
			// case _ =>
			// logger.debug("Evaluating term " + e)
			// Success()
    }
  }

	private def evalBinOp[T <: Term](σ: S, cs: List[SILFunction],
			e0: SILExpression, e1: SILExpression, termOp: (Term, Term) => T, m: Message,
			Q: Term => VerificationResult): VerificationResult =

		evale(σ, cs, e0, m, t0 =>
			evale(σ, cs, e1, m, t1 =>
				Q(termOp(t0, t1))))
        
	private def evalBinOp[T <: Term](σ: S, cs: List[SILFunction],
			e0: SILTerm, e1: SILTerm, termOp: (Term, Term) => T, m: Message,
			Q: Term => VerificationResult): VerificationResult =

		evalt(σ, cs, e0, m, t0 =>
			evalt(σ, cs, e1, m, t1 =>
				Q(termOp(t0, t1))))
        
  private def evalFieldDeref(σ: S,
                             cs: List[SILFunction],
                             rcvr: silAST.expressions.terms.Term,
                             field: silAST.programs.symbols.Field,
                             m: Message,
                             Q: FieldChunk => VerificationResult)
                            : VerificationResult = {

    // println("\n[evalFieldDeref]")
    // println("  m = " + m)
    // println("  m at rcvr = " + (m at rcvr))
                            
    evalt(σ, cs, rcvr, m, tRcvr =>
      if (decider.assert(tRcvr ≠ Null()))
        withFieldChunk(σ.h, tRcvr, field.name, rcvr.toString, m at rcvr, Q)
      else
        Failure(m at rcvr dueTo ReceiverMightBeNull(rcvr.toString, field.name)))
  }

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