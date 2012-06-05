package ch.ethz.inf.pm.silicon

import com.weiglewilczek.slf4s.Logging

import silAST.expressions.{Expression => SILExpression}
import silAST.methods.implementations.{Statement => SILStatement}
// import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}
import silAST.expressions.terms.{Term => SILTerm}
import silAST.programs.symbols.{ProgramVariable => SILProgramVariable}
import silAST.methods.implementations.{
  Block => SILBlock,
  // BasicBlock => SILBasicBlock,
  CFGEdge => SILCFGEdge,
  ControlFlowGraph => SILControlFlowGraph}

import interfaces.{Executor, Evaluator, Producer, Consumer, MapSupport,
		VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State,
		StateFactory, FieldChunk, StateFormatter, HeapMerger}
import interfaces.reporting.{Message}
import interfaces.state.factoryUtils.Ø
// import interfaces.ast.specialVariables.This
// import ast.{Statement, Assign, Variable, VariableExpr, LocalVar, IfStmt,
		// BlockStmt, Assert, Assume, Call, Expression, FieldUpdate, FieldAccess,
		// NewRhs, RValue, Fold, Unfold, PredicateAccess, Access, CallAsync,
		// JoinAsync, Share, Acquire, Release, Unshare, WhileStmt, Free, Credits, Send,
		// Receive, ChannelClass}
// import ast.utils.collections.{SetAnd}
import state.terms
import state.terms.{Term, Null, /* BottomLock, */ True, False /* , Token, LockMode, */
		/* AtLeast, IntLiteral*/, FullPerms => Full }
// import state.terms.utils.¬
// import state.terms.dsl._
import state.{DefaultFieldChunk, DefaultPredicateChunk, /* DefaultTokenChunk, */
		TypeConverter}
import reporting.ErrorMessages.{AssertionMightNotHold, InvocationFailed,
		HeapWriteFailed, HeapReadFailed,
		FoldingFailed, UnfoldingFailed, /* ForkFailed, JoinFailed,
		ShareFailed, AcquireFailed, ReleaseFailed, */ InvalidLockBounds,
		UnshareFailed, MonitorInvariantMightNotHold, SpecsMalformed,
		LoopInvNotPreserved, LoopInvNotEstablished, SendFailed, ReceiveFailed}
import reporting.Reasons.{ExpressionMightEvaluateToFalse,
		InsufficientPermissions, TokenNotWriteable, ChannelMightBeNull,
		OperationRequiresCredits, MightNotBeAboveWaitlevel, ObjectMightBeLocked,
		ObjectMightNotBeLocked, ObjectMightBeShared, ReceiverMightBeNull}
// import reporting.{IfBranching}
import reporting.utils._

/* TODO: Move all required "helper" objects such as stateFactory,
 *       typeConverter, mapSupport, chunkFinder etc. into a separate trait
 *       and mix it into DefaultExecutor, DefaultEvaluator etc.
 */

trait DefaultExecutor[ST <: Store[SILProgramVariable, ST],
											H <: Heap[H],
                      PC <: PathConditions[PC],
											S <: State[SILProgramVariable, ST, H, S]]
		extends Executor[SILProgramVariable, SILControlFlowGraph, ST, H, S]
		{ this:      Logging
            with Evaluator[SILProgramVariable, SILExpression, SILTerm, ST, H, S]
            with Consumer[SILProgramVariable, SILExpression, ST, H, S]
            with Producer[SILProgramVariable, SILExpression, ST, H, S]
            with Brancher =>

	protected val decider: Decider[SILProgramVariable, ST, H, PC, S]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[SILProgramVariable, ST, H, S]
	import stateFactory._

	// protected val permissionFactory: PermissionFactory[P]
	// import permissionFactory._

	// protected val lockSupport: LockSupport[ST, H, S]
	// protected val creditSupport: CreditSupport[ST, H, S]

	protected val typeConverter: TypeConverter
	import typeConverter.toSort

	protected val heapMerger: HeapMerger[H]
	import heapMerger.merge

	// protected val mapSupport: MapSupport[V, ST, H, S]
	// import mapSupport.update

	protected val chunkFinder: ChunkFinder[H]
	import chunkFinder.withFieldChunk

	protected val stateFormatter: StateFormatter[SILProgramVariable, ST, H, S, String]

	protected val config: Config

  def exec(σ: S, cfg: SILControlFlowGraph, m: Message)
          (Q: S => VerificationResult)
          : VerificationResult =

		exec(σ, cfg.startNode, m)(Q)

  /* Continues the execution by following the given edge. The target block
   * is only executed if the edge condition does not contradict with the
   * given state.
   */
  private def follow(σ: S, edge: SILCFGEdge, m: Message)
                   (Q: S => VerificationResult)
                   : VerificationResult = {

    logger.debug("\n[follow] " + edge)
    // println("edge.condition.sourceLocation = " + edge.condition.sourceLocation)
    // println("m at edge.condition = " + (m at edge.condition))
                   
    evale(σ, edge.condition, m at edge.condition, tCond =>
      branch(tCond,
        exec(σ, edge.target, m)(Q),
        Q(σ)))
  }
  
  /* Successively follows each edge in the given list. The state gained
   * by following one node is NOT used when following the next node.
   * That is, each edge in the list is followed using the initially
   * given state σ.
   *
   */
  private def follow(σ: S, edges: Set[SILCFGEdge], m: Message)
                   (Q: S => VerificationResult)
                   : VerificationResult = {

		if (edges.nonEmpty)
			follow(σ, edges.head, m)(_ => /* Notice: The resulting state is discarded. */				
        follow(σ, edges.tail, m)(Q))
		else
      Q(σ)
  }
  
  /* Leaves the given block. A block can be left by two different ways,
   * depending on its role in the enclosing CFG.
   *
   *   - If the block is the end node of the CFG, then Q is executed.
   *     Q could, for example, check a postcondition or an invariant.
   *
   *   - Otherwise, the block's leaving edges (successors) are followed.
   *
   */
  private def leave(σ: S, block: SILBlock, m: Message)
                   (Q: S => VerificationResult)
                   : VerificationResult =

    if (block == block.cfg.endNode) {
      assert(block.successors.isEmpty, "The end node of a CFG is expected to have no successors.")
      Q(σ)
    } else
      follow(σ, block.successors, m)(_ =>
        Success())

  private def exec(σ: S, block: SILBlock, m: Message)
                   (Q: S => VerificationResult)
                   : VerificationResult = {

    logger.debug("\n[exec] " + block.label)
    // println("  block.successors = " + block.successors)
    // println("  σ.π = " + σ.π)
                   
    block match {
      case bb: silAST.methods.implementations.BasicBlock =>
        exec(σ, bb.statements, m)(σ1 =>
          leave(σ1, bb, m)(Q))

      case lb: silAST.methods.implementations.LoopBlock =>
        // println("[execb/LoopBlock]")
        // println("  lb.condition = " + lb.condition)
        // println("  lb.successors = " + lb.successors)
        // println("  lb.writtenVariables = " + lb.writtenVariables)
        
        val BigAnd = ast.utils.collections.BigAnd(lb.implementation.factory) _
        val specsErr = SpecsMalformed withDetails("the loop")
        val inv = lb.invariant
        val invAndGuard = BigAnd(inv :: lb.condition :: Nil, Predef.identity)
        val notGuard =
          lb.implementation.factory.makeUnaryExpression(
            silAST.symbols.logical.Not()(lb.condition.sourceLocation),
            lb.condition,
            lb.condition.sourceLocation,
            Nil)
        val invAndNotGuard = BigAnd(inv :: notGuard :: Nil, Predef.identity)

        val σ1 = σ
        // val bodyγ = Γ(σ1.γ.values.keys.foldLeft(σ1.γ.values)((map, v) => map.updated(v, fresh(v))))
        val bodyγ = Γ(lb.writtenVariables.foldLeft(σ1.γ.values)((map, v) => map.updated(v, fresh(v))))
        val σW = Ø \ (γ = bodyγ)

        /* Verify loop body (including well-formedness check) */
        (produce(σW, fresh, Full(), invAndGuard, specsErr, σ2 =>
          exec(σ2 \ (g = σ1.h), lb.body, m)(σ3 =>
            consume(σ3, Full(), inv, LoopInvNotPreserved, (_, _) =>
              Success())))
          &&
        /* Verify call-site */
        consume(σ1, Full(), inv, LoopInvNotEstablished, (σ2, _) => {
          val σ3 = σ2 \ (g = σ1.h, γ = bodyγ)
          produce(σ3, fresh, Full(), invAndNotGuard, m, σ4 =>
            leave(σ4 \ (g = σ1.g), lb, m)(Q))}))
    }
  }

	private def exec(σ: S, stmts: Seq[SILStatement], m: Message)
                   (Q: S => VerificationResult)
                   : VerificationResult =

		if(stmts.nonEmpty)
			exec(σ, stmts.head, m)(σ1 =>
				exec(σ1, stmts.tail, m)(Q))
		else
			Q(σ)

	private def exec(σ: S, stmt: SILStatement, m: Message)
                  (Q: S => VerificationResult)
                  : VerificationResult = {

		logger.debug("\nEXECUTE " + stmt.toString)
		logger.debug("  " + stmt.getClass.getName)
		logger.debug(stateFormatter.format(σ))

		decider.prover.logComment("")
		decider.prover.logComment(stmt.toString)

		val executed = stmt match {
			// case _ =>
				// // logger.info("Executing " + stmt)
				// Success()

      case silAST.methods.implementations.AssignmentStatement(v, rhs) =>
        evalt(σ, rhs, m, tRhs =>
          Q(σ \+ (v, tRhs)))

      case silAST.methods.implementations.FieldAssignmentStatement(rcvr, field, rhs) =>
        val err = HeapWriteFailed at stmt
        val tRcvr = σ.γ(rcvr)
				// evalt(σ, rcvr, m, tRcvr =>
					if (decider.assert(tRcvr ≠ Null()))
            evalt(σ, rhs, m, tRhs =>
						// execRValue(σ, rhs, m, c1, (σ1, t1, c2) =>
							withFieldChunk(σ.h, tRcvr, field.name, Full(), rcvr.toString, err, fc =>
								Q(σ \- fc \+ DefaultFieldChunk(tRcvr, field.name, tRhs, fc.perm))))
					else
						Failure(err dueTo ReceiverMightBeNull(rcvr.toString, field.name))

      case silAST.methods.implementations.InhaleStatement( a) =>
        // eval(σ, e, m, c, (t, c1) =>
					// assume(t, c1, (c2: C) =>
						// Q(σ, c2)))
        produce(σ, fresh, Full(), a, m, σ1 =>
          Q(σ1))

		  //  TODO: integrate message from exhale statement into error message
      case silAST.methods.implementations.ExhaleStatement(a,msg) =>
        // logger.error("\n[exec/exhale]")
        // logger.error("  stmt = " + stmt)
        // logger.error("  stmt.sourceLocation = " + stmt.sourceLocation)
        // logger.error("  a = " + a)
        // logger.error("  a.sourceLocation = " + a.sourceLocation)
        consume(σ, Full(), a, AssertionMightNotHold(stmt), (σ1, _) =>
          Q(σ1))

			case call @ silAST.methods.implementations.CallStatement(lhs, meth, args) =>
				// val meth = call.m
        val BigAnd = ast.utils.collections.BigAnd(meth.expressionFactory) _

				// evalt(σ, rcvr, m, tRcvr =>
					// if (decider.assert(tRcvr ≠ Null()))
						evalts(σ, args, m, tArgs => {
							// val insγ = Γ(((This, t0) :: meth.ins.zip(tArgs)).toMap)
              /* TODO: Remove hack! */
              // val This = σ.γ.values.keys.find(_.name == "this").get
              // println("\n[Executor/CallStatement]")
              // println("  This = " + This)
              // println("  σ.γ.values = " + σ.γ.values)
              // println("  σ.γ.values.contains = " + σ.γ.values.contains(This))
              /* TODO: Can variable substitution be used instead of creating insγ? */
              // val xs: Seq[(SILProgramVariable, Term)] = (This, tRcvr) +: meth.signature.parameters.variables.drop(1).zip(tArgs)
							// val insγ = Γ(xs.toMap)
							val insγ = Γ(meth.signature.parameters.variables.zip(tArgs))
              // println("  insγ.values = " + insγ.values)
              // println("  insγ.values.contains = " + insγ.values.contains(This))
              // println("  insγ = " + insγ)
							val err = InvocationFailed(meth.name, call.sourceLocation)
              val pre = BigAnd(meth.signature.precondition, Predef.identity)
							consume(σ \ insγ, Full(), pre, err, (σ1, _) => {
								val outsγ = Γ(meth.signature.results.map(v => (v, fresh(v))).toMap)
								val σ2 = σ1 \+ outsγ \ (g = σ.h)
                val post = BigAnd(meth.signature.postcondition, Predef.identity)
								// val post = ast.And(
									// meth.post,
									// ast.LockChangeExpr(meth.lockchange).setPos(meth.pos))
								produce(σ2, fresh, Full(), post, err, σ3 => {
                  val lhsγ = Γ(lhs.zip(meth.signature.results)
                                  .map(p => (p._1, σ3.γ(p._2))).toMap)
									Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ))})})})
                // Q(σ)})})
					// else
						// Failure(m at stmt dueTo ReceiverMightBeNull(rcvr.toString, meth.name)))

      case silAST.methods.implementations.NewStatement(v, dt) =>
        assert(v.dataType == dt, "Expected same data type for lhs and rhs.")
        Q(σ \+ (v, fresh(v)))
            

			// /* TODO: Assert should not forward Q but 'terminate' after the assertion
			 // *       and only then invoke Q. Currently, assert b ==> acc(x) will
			 // *       branch and will thus invoke Q twice, which is inefficient.
			 // *       BUT: Might be smarter to make this a cli option, because it
			 // *       sometimes might be necessary to continue for each branch if
			 // *       the assertion is used to help the prover.
			 // */
			// case Assert(a) =>
				// val err = AssertionMightNotHold(stmt)

				// a match {
					// case _: ast.False =>
						// if (decider.checkSmoke)
							// Success(c)
						// else
							// Failure(err at a dueTo ExpressionMightEvaluateToFalse, c)

					// /* TODO: Respect --disableSubsumption option */
					// case _: Credits =>
						// eval(σ, a, m, c, (t, c1) =>
							// if (decider.assert(t))
								// Q(σ, c1)
							// else
								// Failure(err at a dueTo ExpressionMightEvaluateToFalse, c1))

					// case _ =>
						// if (config.disableSubsumption)
							// decider.prover.push("disableSubsumption")
						// consume(σ, Full, a, AssertionMightNotHold(stmt), c, (σ1, _, c1) => {
							// if (config.disableSubsumption)
								// decider.prover.pop("disableSubsumption")
							// Q(σ, c1)})
				// }

			// case LocalVar(v) => Q(σ \+ (v, fresh(v)), c)

			// case ass @ Assign(lhs, rhs) =>
				// assert(ass.declares.isEmpty, /* @elidable */
						// "Expect Assign.declares to be empty, but was " + ass.declares)
				// assert(ass.targets.size == 1, /* @elidable */
						// ("Expected Assign.targets to contain exactly one element, but contained " + ass.targets.size))

				// execRValue(σ, rhs, m, c, (σ1, t, c1) =>
					// Q(σ1 \+ (lhs, t), c1))

			// case FieldUpdate(FieldAccess(e0, id), rhs) =>
				// val err = HeapWriteFailed at stmt
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null())) {
						// execRValue(σ, rhs, m, c1, (σ1, t1, c2) =>
							// withFieldChunk(σ1.h, t0, id, Full, e0, err, c2, fc =>
								// Q(σ1 \- fc \+ DefaultFieldChunk(t0, id, t1, fc.perm), c2)))}
					// else
						// Failure(err dueTo ReceiverMightBeNull(e0, id), c1))

			// case call @ CallAsync(lhs, e0, id, args) =>
				// val meth = call.m
				// assert(meth != null, "Call.m may not be null") /* @elidable */
				// assert(call.declares == Nil, /* @elidable */
						// ("Call.declares is expected to be Nil, but was " + call.declares))

				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// /* TODO: Isn't σ.γ(lhs) sufficient, i.e. do we have to evaluate
						 // *       lhs? Well, eval'ing is more general and is definitely not
						 // *        causing any trouble.
						 // */
						// eval(σ, lhs, m, c1, (tLhs, c2) => {
							// /* TODO: If the fields are guaranteed to exist, e.g. by having
							// *        them default values, we wouldn't need to distinguish
							// *        here and could just remove them from the heap.
							// */
							// val h = decider.getFieldChunk(σ.h, tLhs, "joinable") match {
								// case Some(fc) => σ.h - fc
								// case None => σ.h}
							// val h1 = decider.getChunk(σ.h, tLhs, "$env") match {
								// case Some(tc: DefaultTokenChunk[P, H]) => h - tc
								// case None => h}
							// val σ1 = σ \ h1
							// evals(σ1, args, m, c2, (tArgs, c3) => {
								// val insγ = Γ(((This, t0) :: meth.ins.zip(tArgs)).toMap)
								// val tEnv = Token[P, H](meth, σ.h, t0, tArgs)
								// val fc = DefaultFieldChunk(tLhs, "joinable", True(), Eps)
								// val tc = DefaultTokenChunk(tLhs, tEnv)
								// val err = ForkFailed(call)
								// consume(σ1 \ insγ, Full, meth.pre, err, c3, (σ2, _, c4) =>
									// assume(tLhs ≠ Null(), c4, (c5: C) =>
										// Q(σ2 \ (g = σ.g, γ = σ.γ) \+ fc \+ tc, c5)))})})
					// else
						// Failure(m at stmt dueTo ReceiverMightBeNull(e0, id), c1))

			// case join @ JoinAsync(lhs, e0) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// decider.getFieldChunk(σ.h, t0, "joinable") match {
						// case Some(fc) if fc.value == True() =>
							// /* TODO: Declare TokenSupport and use σ.h.tokens.get(...)
							 // *        - we wouldn't have to either cast or match here to get
							 // *          the desired chunk type
							 // *        - we remove the fragile coupling via literal "$env"
							 // */
							// val tc = (decider.getChunk(σ.h, t0, "$env")
													     // .get.asInstanceOf[DefaultTokenChunk[P, H]])
							// val meth = tc.token.m
							// val mγ = Γ( 	 ((This, tc.token.t0)
												 // ::  meth.ins.zip(tc.token.tArgs)
												 // ::: meth.outs.map(v => (v, fresh(v)))).toMap)
							// val σ1 = σ \ (g = tc.token.h) \ mγ
							// val post = ast.And(
								// meth.post,
								// ast.LockChangeExpr(meth.lockchange).setPos(meth.pos))
							// produce(σ1, fresh, Full, post, m, c1, (σ2, c2) => {
								// val lhsγ = Γ(lhs.map(_.asVariable)
																// .zip(meth.outs)
																// .map(p => (p._1, σ2.γ(p._2))).toMap)
								// Q(σ2 \ (g = σ.g, γ = σ.γ + lhsγ)
										 // \- tc \- fc
										 // \+ DefaultFieldChunk(t0, "joinable", False(), Eps),
									// c2)})
						// case other =>
							// Failure(JoinFailed at stmt withDetails(e0) dueTo TokenNotWriteable, c1)})

			// case Fold(Access(pa @ PredicateAccess(e0, id), p0)) =>
				// assert(pa.p != null, /* @elidable */
						// "Expected Access.ma to not be null")

				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// evalp(σ, p0, m, c1, (pt, c2) =>
							// decider.isValidFraction(pt) match {
								// case None =>
									// val err = FoldingFailed(stmt)
									// val insγ = Γ((This -> t0))
									// consume(σ \ insγ, pt, pa.p.body, err, c2, (σ1, snap, c3) => {
										// /* Producing Access is unfortunately not an option here
										 // * since the following would fail due to productions
										 // * starting in an empty heap:
										 // *
										 // *   predicate V { acc(x) }
										 // *
										 // *   function f(a: int): int
										 // *	   requires rd(x)
										 // * 	 { x + a }
										 // *
										 // *   method test(a: int)
										 // *     requires ... ensures ...
										 // *   { fold acc(V, f(a)) }
										 // *
										 // * Fold would fail since acc(V, f(a)) is produced in an
										 // * empty and thus f(a) fails due to missing permissions to
										 // * read x.
										 // *
										 // * TODO: Use heap merge function here!
										 // */
										// val (h, t, perm) =
											// decider.getPredicateChunk(σ1.h, t0, id) match {
												// case Some(pc) =>
													// (σ1.h - pc, pc.snap ≡ snap, pc.perm + pt)
												// case None =>
													// (σ1.h, True(), pt)}

										// assume(t, c3, (c4: C) =>
											// Q(σ \ h \+ DefaultPredicateChunk(t0, id, snap, perm), c4))})
								// case Some(errmsg) =>
									// Failure(errmsg at stmt withDetails (e0, id), c2)})
					// else
						// Failure(m at stmt dueTo ReceiverMightBeNull(e0, id), c1))

			// case Unfold(acc @ Access(pa @ PredicateAccess(e0, id), p0)) =>
				// assert(pa.p != null, /* @elidable */
						// "Expected Access.ma to not be null")

				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// evalp(σ, p0, m, c1, (pt, c2) =>
							// decider.isValidFraction(pt) match {
								// case None =>
									// val insγ = Γ((This -> t0))
									// consume(σ, Full, acc, UnfoldingFailed, c2, (σ1, snap, c3) =>
										// produce(σ1 \ insγ, snap, pt, pa.p.body, m, c3, (σ2, c4) =>
											// Q(σ2 \ σ.γ, c4)))
								// case Some(errmsg) =>
									// Failure(errmsg at stmt withDetails (e0, id), c2)})
					// else
						// Failure(m at stmt dueTo ReceiverMightBeNull(e0, id), c1))

			// /* TODO: Separate and limit
			 // *  - one rule only for "share c between waitlevel and mu's"
			 // *  - second rule only for "share c between mu's and mu's",
			 // *    but where waitlevel and lockbottom may not occur
			 // */
			// case Share(e0, lbs, ubs) =>
				// assert(!ubs.exists(_.isInstanceOf[ast.MaxLock]), /* @elidable */
						// "Sharing below waitlevel isn't yet supported.")

				// /* Sharing requires acc(e0.mu) even if --disableDeadlockChecks is used,
				 // * because the mu-field is used to prevent objects from being shared
				 // * multiple times. I don't know of a way of sharing an object multiple
				 // * times to create an inconsistency, but the possibility nevertheless
				 // * sounds dubious to me and I'd like to avoid it.
				 // */

				// val err = ShareFailed(e0) at stmt
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// withFieldChunk(σ.h, t0, "mu", Full, e0, err, c1, fc =>
							// if (decider.assert(fc.value ≡ BottomLock())) {
								// val tMu1 = fresh("$mu")

								// /* When sharing c between lb and ub, the correct proceeding
								 // * order is:
								 // *  1. assert c.mu != lockbottom
								 // *  2. assert l << u for all l in lb and all u in ub
								 // *  3. remove c.mu from h, add fresh c.mu chunk, update
								 // *     mu-function
								 // *  ??????????? Can't steps 2 and 3 be switched? ???????????
								 // *  4. eval and assume l << c && c << u forall l in lb, u
								 // *     in ub
								 // *  5. consume monitor invariant
								 // */

								// /* It is always crucial that the mu-version is incremented
								 // * (lockSupport.MuUpdate) before a mu-term depending on it
								 // * (lockSupport.Mu) is added to the path conditions, since
								 // * the latter will otherwise use the wrong mu-version.
								 // */
								// update(σ \- fc, lockSupport.Mu, t0, c1, (σ1, c2) => {
									// val σ2 = σ1 \+ DefaultFieldChunk(t0, "mu", tMu1, fc.perm)
									// val ts: Set[Term] =
										// /* Why is σ1 used here and not σ2? */
										// Set(lockSupport.Mu(σ1.h, t0, tMu1),
												// lockSupport.Holds(σ1.h, t0, LockMode.None),
												// tMu1 ≠ BottomLock())
									// assume(ts, c2, (c3: C) =>
										// establishOrdering(σ2, e0, lbs, ubs, m, c3, c4 => {
											// val err = MonitorInvariantMightNotHold(stmt)
											// val inv = e0.typ.typ.inv
											// val insγ = Γ((This -> t0))
											// consume(σ2 \ insγ, Full, inv, err, c4, (σ3, _, c5) =>
												// Q(σ3 \ σ2.γ, c5))}))})}
							// else
								// Failure(err dueTo ObjectMightBeShared, c1))
					// else
						// Failure(err dueTo ReceiverMightBeNull(e0, "mu"), c1))

			// case Acquire(e0, lm) =>
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// consume(σ, Full, astUtils.MaxLockLess(e0), AcquireFailed(e0) at stmt dueTo(MightNotBeAboveWaitlevel, true), c1, (_, _, c2) =>
							// if (decider.assert(lockSupport.Holds(σ.h, t0, LockMode.None))) {
									// val insγ = Γ((This -> t0))
									// val inv = e0.typ.typ.inv
									// val lmt = evallm(lm)
									// val pt = if (lmt == LockMode.Write) Full else Eps
									// update(σ, lockSupport.Holds, t0, c2, (σ1, c3) =>
										// assume(lockSupport.Holds(σ1.h, t0, lmt), c3, (c4: C) =>
											// produce(σ1 \ insγ, fresh, pt, inv, m, c4, (σ2, c5) =>
												// Q(σ2 \ σ1.γ, c5))))}
							// else
								// Failure(AcquireFailed(e0) at stmt dueTo ObjectMightBeLocked, c2))
					// else
						// Failure(AcquireFailed(e0) at stmt dueTo ReceiverMightBeNull(e0, "mu"), c1))

			// case Release(e0, lm) =>
				// val id = "mu"
				// val err = ReleaseFailed(e0) at stmt
				// val monInvErr = MonitorInvariantMightNotHold(stmt)
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null())) {
						// val lmt = evallm(lm)
						// if (decider.assert(lockSupport.Holds(σ.h, t0, lmt))) {
							// val insγ = Γ((This -> t0))
							// val inv = e0.typ.typ.inv
							// val pt = if (lmt == LockMode.Write) Full else Eps
							// consume(σ \ insγ, pt, inv, monInvErr, c1, (σ1, _, c2) =>
								// update(σ1 \ σ.γ, lockSupport.Holds, t0, c2, (σ2, c3) =>
									// assume(lockSupport.Holds(σ2.h, t0, LockMode.None), c3, (c4: C) =>
										// Q(σ2, c4))))}
						// else
							// Failure(err dueTo ObjectMightNotBeLocked(lm), c1)}
					// else
						// Failure(err dueTo ReceiverMightBeNull(e0, id), c1))

			// case Unshare(e0) =>
				// val id = "mu"
				// val err = UnshareFailed(e0) at stmt
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null()))
						// /* Unsharing objects multiple times is prohibited by requiring
						 // * that the object is write-locked and then setting its lock-status
						 // * to LockMode.None.
						 // * Hence, in contrast to Share we can skip checking proper access
						 // * to e0.mu here, in case disableDeadlockChecks is used.
						 // */
						// if (   config.disableDeadlockChecks
						    // || decider.assertWriteAccess(σ.h, t0, "mu"))
							// if (decider.assert(lockSupport.Holds(σ.h, t0, LockMode.Write)))
								// update(σ, lockSupport.Holds, t0, c1, (σ1, c2) =>
									// update(σ1, lockSupport.Mu, t0, c2, (σ2, c3) => {
										// val ts: Set[Term] =
											// Set(lockSupport.Holds(σ2.h, t0, LockMode.None),
													// lockSupport.Mu(σ2.h, t0, BottomLock()))
										// assume(ts, c3, (c4: C) =>	{
											// val nfc = DefaultFieldChunk(t0, id, BottomLock(), Full)
											// Q(σ2 \+ nfc, c4)})}))
							// else
								// Failure(err dueTo ObjectMightNotBeLocked(ast.WriteLockMode), c1)
						// else
							// Failure(err dueTo InsufficientPermissionTerm(e0, id), c1)
					// else
						// Failure(err dueTo ReceiverMightBeNull(e0, id), c1))

			// case ws @ WhileStmt(guard, _, _, _, body) =>
				// assert(ws.newInvs.isEmpty, /* @elidable */
						// "Expected WhileStmt.newInvs to be empty, but was " + ws.newInvs)

				// /* Order of arguments to ast.And is important! The inv must be the
				 // * first conjunct, because it may contain access assertions which are
				 // * required in order for the guard to be well-defined.
				 // */
				// val lkch = ast.LockChangeExpr(ws.lkch).setPos(ws.pos)
				// val inv = ast.And(ws.inv, lkch)
				// val invAndGuard = ast.And(inv, guard)
				// val invAndNotGuard = ast.And(inv, ast.Not(guard))
				// val specsErr = SpecsMalformed withDetails("the loop")

				// /* Havoc local variables that are assigned to in the loop body but
				 // * that have been declared outside of it, i.e. before the loop.
				 // */
        // val bodyγ =
          // Γ((ws.targets -- ws.declares)
							// .foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))

				// /* Verify loop body (including well-formedness check) */
				// val σW = Ø \ (γ = bodyγ)
				// (produce(σW, fresh, Full, invAndGuard, specsErr, c, (σ1, c1) =>
					// exec(σ1 \ (g = σ1.h), body, m, c1, (σ2, c2) =>
						// consume(σ2, Full, inv, LoopInvNotPreserved, c2, (σ3, _, c3) =>
							// Success(c3))))
					// &&
				// /* Verify call-site */
				// consume(σ, Full, inv, LoopInvNotEstablished, c, (σ1, _, c1) => {
					// val σ2 = σ1 \ (g = σ.h, γ = bodyγ)
					// produce(σ2, fresh, Full, invAndNotGuard, m, c1, (σ3, c2) =>
						// Q(σ3 \ (g = σ.g), c2))}))

      // case Free(e0) =>
				// val err = HeapWriteFailed at stmt
				// eval(σ, e0, m, c, (t0, c1) =>
					// if (decider.assert(t0 ≠ Null())) {
            // assert(e0.typ != null, /* @elidable */
                // "Expected ast.Free.e0.typ to be non-null: " + stmt + ", "+ e0)
            // assert(e0.typ.typ != null, /* @elidable */
                // "Expected ast.Free.e0.typ.typ to be non-null: " + stmt + ", " + e0 + ", " + e0.typ)

            // var σ1 = σ /* Iteratively updated by removing field chunks */
            // var result: VerificationResult = Success(c1) /* Current iter. result */

            // /* TODO: Rewrite in a functional, clearer way */
            // e0.typ.typ.fieldMembers.forall(m => {
							// /* Predicates don't need to be considered since they must be
							 // * unfolded in order to have write-access to all fields.
							 // */
              // result = decider.getFieldChunk(σ1.h, t0, m.id) match {
								// case Some(fc) =>
									// if (decider.assertWriteAccess(fc.perm)) {
                    // σ1 = σ1 \- fc
                    // Success(c1)}
									// else
										// Failure(err dueTo InsufficientPermissionTerm(e0, m.id), c1)
								// case None =>
                  // Failure(err dueTo InsufficientPermissionTerm(e0, m.id), c1)}
							// !result.isFatal})

            // result && Q(σ1, c1)}
					// else
						// Failure(err dueTo ReceiverMightBeNull("free " + e0), c1))

      // case send @ Send(e, args) =>
				// val ch = e.typ.typ.asInstanceOf[ChannelClass].ch
				// val post = Credits(e, ast.IntLiteral(1))
				// val err = SendFailed(send) at stmt
				// eval(σ, e, m, c, (tCh, c1) =>
					// if (decider.assert(tCh ≠ Null()))
						// evals(σ, args, m, c1, (tArgs, c2) => {
							// val insγ = Γ((This, tCh) :: ch.params.zip(tArgs))
							// consume(σ \ insγ, Full, ch.where, err, c2, (σ1, _, c3) =>
								// produce(σ1 \ σ.γ, fresh, Full, post, m, c3, (σ2, c4) => {
									// Q(σ2, c4)}))})
					// else
						// Failure(err dueTo ReceiverMightBeNull("send " + e), c1))

			// case receive @ Receive(e, outs) =>
				// val ch = e.typ.typ.asInstanceOf[ChannelClass].ch
				// val err = ReceiveFailed(e) at receive

				// eval(σ, e, m, c, (tCh, c1) =>
					// if (decider.assert(tCh ≠ Null()))
						// if (decider.assert(AtLeast(creditSupport.Credits(σ.h, tCh), 1)))
							// consume(σ, Full, Credits(e, 1), err dueTo OperationRequiresCredits, c1, (σ1, _, c2) =>
								// withFieldChunk(σ1.h, tCh, "mu", e, err, c2, fc =>
									// if (decider.assert(lockSupport.MaxLockLess(σ1.h, fc.value))) {
										// val rγ = Γ(   (This, tCh)
															 // :: ch.params.map(v => (v, fresh(v))))
										// produce(σ1 \ rγ, fresh, Full, ch.where, m, c2, (σ2, c3) => {
											// val lhsγ = Γ(outs.map(_.asVariable)
																			 // .zip(ch.params)
																			 // .map(p => (p._1, σ2.γ(p._2))))
											// Q(σ2 \ (σ1.γ + lhsγ) , c3)})}
									// else
											// Failure(err dueTo MightNotBeAboveWaitlevel, c2)))
						// else
							// Failure(err dueTo OperationRequiresCredits, c1)
					// else
						// Failure(err dueTo ChannelMightBeNull, c1))
		}

		// logger.debug("EXECUTED? " + executed.isSuccess))
		// println("executed = " + executed)

		executed
	}

	// protected def execRValue(σ: S, rv: RValue, m: Message,
			// Q: (S, Term) => VerificationResult): VerificationResult = rv match {

		// /* Expression */
		// case e: Expression =>
			// eval(σ, e, HeapReadFailed, t =>
				// Q(σ, t))

		// /* new SomeClass() */
		// case nr @ NewRhs(id, inits, lbs, ubs) =>
			// /* TODO: It would probably be helpful to declare that the new object is
			 // *       not equal to all other objects in the current scope, i.e. to add
			 // *       the corresponding terms to the path conditions.
			 // */
			// assert(nr.typ != null, /*@ elidable */
					// "Expected NewRhs.typ to be non-null.")

			// val vRcvr = new ast.Variable(nr.name, nr.typ).setPos(nr.pos)
			// val eRcvr = new VariableExpr(vRcvr).setPos(nr.pos)
			// val tRcvr = fresh(eRcvr)
			// val eInits = inits.map(_.e)

			// /* Only works if each field occurs at most once in n.inits. This is
			 // * currently (2011-02-18) ensured by Chalice's typechecker.
			 // * If that is not guaranteed, consider SeqLike.lastIndexWhere instead of
			 // * SeqLike.findIndexOf.
			 // */
			// evals(σ, eInits, m, c, (tInits, c1) => {
				// var tMuFct: Term = True()

				// /* Initialise fields */
				// val fieldChunks: Map[String, FieldChunk[P]] =
					// nr.typ.typ.fieldMembers.map(f => {
						// val i = inits.findIndexOf(_.id == f.id)
						// val t =
							// if (i == -1) evall(f.defaultValue).convert(toSort(f.typ))
							// else tInits(i)
						// if (f.id == "mu")
							// tMuFct = lockSupport.Mu(σ.h, tRcvr, t)

						// (f.id, DefaultFieldChunk(tRcvr, f.id, t, Full))}).toMap

				// val (h, tMerged) = merge(σ.h, H(fieldChunks.values))
				// /* TODO: Should we use LM.release here instead of lockSupport.Holds?
				 // * Syxc might conclude from
				 // *   assume waitlevel << c1
				 // *   var c2 := new Cell
				 // * that
				 // *   assert c2 << c1
				 // * holds. I haven't tested this yet.
				 // */
				// val σ1 = σ \ h
				// var ts = tMerged
				// ts += tRcvr ≠ Null()
				// ts += tMuFct
				// ts += lockSupport.Holds(σ1.h, tRcvr, LockMode.None)

				// nr.typ.typ match {
					// case ChannelClass(_) =>
						// val tMu = fieldChunks("mu").value
						// ts += tMu ≠ BottomLock()
						// ts += lockSupport.MaxLockLess(σ1.h, tMu)
						// assume(ts, c1, (c2: C) =>
							// establishOrdering(σ1 \+ (vRcvr, tRcvr), eRcvr, lbs, ubs, m, c2, c3 =>
								// Q(σ1, tRcvr, c3)))

					// case _ =>
						// assume(ts, c1, (c2: C) =>
							// Q(σ1, tRcvr, c2))}})}

	// protected def establishOrdering(σ: S, e: Expression,
																	// lbs: List[Expression], ubs: List[Expression],
																	// m: Message, Q: => VerificationResult)
																 // : VerificationResult = {

		// /* TODO:
		 // *   Highly inefficient, since each bound is evaluated
		 // *   multiple times, e0 also, overall
		 // *     |lbs|*|ubs| + 2*(|lbs| + |ubs|)
		 // *   evalutations, each one possibly including a mu-field
		 // *   lookup.
		 // *
		 // *   a) We could evaluate all bounds once and then consume
		 // *      comparisons on terms instead of expressions. This is
		 // *      currently not possible, since prod/cons/eval only
		 // *      accept expressions and there is no e.g. t1 << t2
		 // *      expression.
		 // *      Possible solution: have ast.TermExpr <: Expr, but
		 // *      that couples AST to Term.
		 // *
		 // *   b) Reduce complexity by saving repeated mu-lookups.
		 // *      From
		 // *        share o between l1,...ln and u1,...,um
		 // *      create
		 // *        var $ml1: mu := l1.mu
		 // *        ...
		 // *        var $mln: mu := ln.mu
		 // *        ...
		 // *        var $mum: mu := um.mu
		 // *      exec that and then consume
		 // *        $ml1 << $mu1 && ... && $mln << $mum
		 // *      Problem: We must filter first and then separatly
		 // *      handle waitlevel-expressions.
		 // *      Due to all the exec-overhead we probably don't gain
		 // *      much efficiency anyway.
		 // */

		// /* TODO: Same code as in ChaliceASTConverter, reuse! */
		// val f = (e0: Expression, e1: Expression) =>
			// if (e0.isInstanceOf[ast.MaxLock]) {
				// assert(e1.isInstanceOf[ast.FieldAccess], "Expected waitlevel << e.mu")
				// ast.MaxLockLess(e0.asInstanceOf[ast.MaxLock], e1).setPos(e.pos)
			// } else if (e1.isInstanceOf[ast.MaxLock]) {
				// assert(e0.isInstanceOf[ast.FieldAccess], "Expected waitlevel << e.mu")
				// ast.MaxLockLess(e1.asInstanceOf[ast.MaxLock], e0).setPos(e.pos)
			// } else {
				// assert(e0.isInstanceOf[ast.FieldAccess] && e1.isInstanceOf[ast.FieldAccess], "Expected e0.mu << e1.mu")
				// ast.LockLess(e0, e1).setPos(e.pos)
			// }

		// /* TODO: Check if "share c.mu" is valid Chalice code */
		// val faMu = ast.FieldAccess(e, "mu").setPos(e.pos)

		// val pre =
			// SetAnd(lbs.flatMap(lb =>
				// ubs.map(f(lb, _).setPos(lb.pos))))

		// val post =
			// ast.And(
				// SetAnd(
					// lbs.map(f(_, faMu).setPos(faMu.pos))),
				// SetAnd(
					// ubs.map(f(faMu, _).setPos(faMu.pos))))

		// consume(σ, Full, pre, InvalidLockBounds, c, (_, _, c1) =>
			// eval(σ, post, m, c1, (tPost, c2) =>
				// assume(tPost, c2, (c3: C) =>
					// Q(c3))))
	// }

	// /* TODO: Extract, move into utilities object */
	// implicit def expressionToVariable(v: VariableExpr): Variable = v.asVariable
	// implicit def intToAst(i: Int): ast.IntLiteral = ast.IntLiteral(i)
	// implicit def intToTerm(i: Int): IntLiteral = IntLiteral(i)

	// /* TODO: Move into appropriate utility package */
	// protected object astUtils {
		// def MuFieldAccess(e: Expression) = {
			// val fa = ast.FieldAccess(e, "mu")
			// fa.f = e.typ.typ.members.find(_.id == "mu").get.asInstanceOf[ast.FieldMember]
			// fa.setPos(e.pos)

			// fa
		// }

		// def MaxLockLess(e: Expression) = {
			// val mll = ast.MaxLockLess(MuFieldAccess(e))
			// mll.setPos(e.pos)

			// mll
		// }
	// }
}