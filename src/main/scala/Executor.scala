package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{Internal, AssertionMalformed, LoopInvariantNotPreserved,
    LoopInvariantNotEstablished, UnsafeCode, AssertionViolated, InvocationFailed, FoldFailed,
    UnfoldFailed}
import sil.verifier.reasons.{ReceiverNull}
import interfaces.{Executor, Evaluator, Producer, Consumer, VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
    HeapMerger}
import interfaces.reporting.{/*Message,*/ TraceView}
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.terms.implicits._
import state.{DirectFieldChunk,
    DirectPredicateChunk, TypeConverter, DirectChunk, NestedFieldChunk,
    NestedPredicateChunk}
import reporting.{DefaultContext, Executing, IfBranching, Description, BranchingDescriptionStep,
    ScopeChangingDescription}

trait DefaultExecutor[ST <: Store[ST],
                      H <: Heap[H],
											PC <: PathConditions[PC],
                      S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Executor[ast.ControlFlowGraph, ST, H, S, DefaultContext[ST, H, S], TV]
		{ this: Logging with Evaluator[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Consumer[PermissionsTuple, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Producer[PermissionsTuple, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]

	protected val decider: Decider[PermissionsTuple, ST, H, PC, S, C]
	import decider.{fresh, assume, inScope}
							
	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val typeConverter: TypeConverter
	protected val heapMerger: HeapMerger[H]

	protected val chunkFinder: ChunkFinder[ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshReadVar

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config

  def exec(σ: S, cfg: ast.ControlFlowGraph, c: C, tv: TV)
          (Q: (S, C) => VerificationResult)
          : VerificationResult =

    exec(σ, cfg.startNode, c, tv)(Q)

  /* Continues the execution by following the given edge. The target block
   * is only executed if the edge condition does not contradict with the
   * given state.
   */
  private def follow(σ: S, edge: ast.CFGEdge, c: C, tv: TV)
                    (Q: (S, C) => VerificationResult)
                    : VerificationResult = {

    logger.debug("\n[follow] " + edge)

    eval(σ, edge.condition, Internal(edge.condition), c, tv)((tCond, c1) =>
      /* TODO: Use FollowEdge instead of IfBranching */
      branch(tCond, c1, tv, IfBranching[ST, H, S](edge.condition, tCond),
        (c2: C, tv1: TV) => exec(σ, edge.target, c2, tv1)(Q),
        (c2: C, tv1: TV) => Q(σ, c2)))
  }

  /* Successively follows each edge in the given list. The state gained
   * by following one node is NOT used when following the next node.
   * That is, each edge in the list is followed using the initially
   * given state σ.
   */
  private def follow(σ: S, edges: Set[ast.CFGEdge], c: C, tv: TV)
                    (Q: (S, C) => VerificationResult)
                    : VerificationResult = {

    if (edges.nonEmpty)
      follow(σ, edges.head, c, tv)((_, c1) => /* Notice: The resulting state is discarded. */
        follow(σ, edges.tail, c1, tv)(Q))
    else
      Q(σ, c)
  }

  /* Leaves the given block. A block can be left by two different ways,
   * depending on its role in the enclosing CFG.
   *
   *   - If the block is the end node of the CFG, then Q is executed.
   *     Q could, for example, check a postcondition or an invariant.
   *
   *   - Otherwise, the block's leaving edges (successors) are followed.
   */
  private def leave(σ: S, block: ast.Block, c: C, tv: TV)
                   (Q: (S, C) => VerificationResult)
                   : VerificationResult =

    if (block == block.cfg.endNode) {
      assert(block.successors.isEmpty, "The end node of a CFG is expected to have no successors.")
      Q(σ, c)
    } else
      follow(σ, block.successors, c, tv)((_, c1) => Success[C, ST, H, S](c1))

  private def exec(σ: S, block: ast.Block, c: C, tv: TV)
                  (Q: (S, C) => VerificationResult)
                  : VerificationResult = {

    logger.debug("\n[exec] " + block.label)

    block match {
      case bb: semper.sil.ast.methods.implementations.BasicBlock =>
        exec(σ, bb.statements, c, tv)((σ1, c1) =>
          leave(σ1, bb, c1, tv)(Q))

      case lb: semper.sil.ast.methods.implementations.LoopBlock =>
        val BigAnd = ast.utils.collections.BigAnd(lb.implementation.factory) _
        val inv = lb.invariant
        val invAndGuard = BigAnd(inv :: lb.condition :: Nil, Predef.identity)
        val notGuard =
          lb.implementation.factory.makeUnaryExpression(
            semper.sil.ast.symbols.logical.Not()(lb.condition.sourceLocation),
            lb.condition,
            lb.condition.sourceLocation,
            Nil)
        val invAndNotGuard = BigAnd(inv :: notGuard :: Nil, Predef.identity)

        /* Havoc local variables that are assigned to in the loop body but
         * that have been declared outside of it, i.e. before the loop.
         */
        val γBody = Γ(lb.writtenVariables.foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))
        val (rdVarBody, rdVarBodyConstraints) = freshReadVar("$LoopRd")
        val cBody = c.setCurrentRdPerms(ReadPerms(rdVarBody))
        val σBody = Ø \ (γ = γBody)

        (inScope {
          /* Verify loop body (including well-formedness check) */
          val (c0, tv0) = tv.splitOffLocally(c, BranchingDescriptionStep[ST, H, S]("Loop Invariant Preservation"))
          assume(rdVarBodyConstraints, cBody)
          produce(σBody, fresh,  FullPerms(), invAndGuard, AssertionMalformed(inv), c0, tv0)((σ1, c1) =>
            exec(σ1 \ (g = σ1.h), lb.body, c1, tv0)((σ2, c2) =>
              consume(σ2,  FullPerms(), inv, LoopInvariantNotPreserved(inv), c2, tv0)((σ3, _, _, c3) =>
                Success[C, ST, H, S](c3))))}
            &&
          inScope {
            /* Verify call-site */
            val tv0 = tv.stepInto(c, Description[ST, H, S]("Loop Invariant Establishment"))
            val (rdVar, rdVarConstraints) = freshReadVar("$LoopRd", c.currentRdPerms)
            val c0 = (c.setConsumeExactReads(false)
              .setCurrentRdPerms(ReadPerms(rdVar)))
            assume(rdVarConstraints, c0)
            consume(σ,  FullPerms(), inv, LoopInvariantNotEstablished(inv), c0, tv0)((σ1, _, _, c1) => {
              val σ2 = σ1 \ (g = σ.h, γ = γBody)
              produce(σ2, fresh,  FullPerms(), invAndNotGuard, AssertionMalformed(inv), c1, tv0)((σ3, c2) => {
                val c3 = (c2.setConsumeExactReads(true)
                  .setCurrentRdPerms(c.currentRdPerms))
                leave(σ3 \ (g = σ.g), lb, c3, tv)(Q)})})})
    }
  }

  private def exec(σ: S, stmts: Seq[ast.Statement], c: C, tv: TV)
                  (Q: (S, C) => VerificationResult)
                  : VerificationResult =

    if(stmts.nonEmpty)
      exec(σ, stmts.head, c, tv)((σ1, c1) =>
        exec(σ1, stmts.tail, c1, tv)(Q))
    else
      Q(σ, c)

  private def exec(σ: S, stmt: ast.Statement, c: C, tv: TV)
                  (Q: (S, C) => VerificationResult)
                  : VerificationResult = {

    val tv1 = tv.stepInto(c, Executing[ST, H, S](σ, stmt))

    actualExec(σ, stmt, c, tv1)((σ1, c1) => {
      tv1.currentStep.σPost = σ1
      Q(σ1, c1)
    })
  }

	private def actualExec(σ: S, stmt: ast.Statement, c: C, tv: TV)
			    (Q: (S, C) => VerificationResult)
          : VerificationResult = {

		logger.debug("\nEXECUTE " + stmt.toString)
		logger.debug(stateFormatter.format(σ))
		decider.prover.logComment("")
		decider.prover.logComment(stmt.toString)

		val executed = stmt match {
      case ast.Assignment(v, rhs) =>
        eval(σ, rhs, UnsafeCode(stmt), c, tv)((tRhs, c1) =>
          Q(σ \+ (v, tRhs), c1))

      case ast.FieldWrite(rcvr, field, rhs) =>
        val pve = UnsafeCode(stmt)
        val tRcvr = σ.γ(rcvr)
        if (decider.assert(tRcvr !== Null()))
          eval(σ, rhs, pve, c, tv)((tRhs, c1) =>
            withChunk[DirectFieldChunk](σ.h, tRcvr, field.name, FullPerms(), rcvr, pve, c1, tv)(fc =>
              Q(σ \- fc \+ DirectFieldChunk(tRcvr, field.name, tRhs, fc.perm), c1)))
        else
          Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(rcvr), c, tv)

      case ast.Inhale(a) =>
        produce(σ, fresh, FullPerms(), a, Internal(stmt), c, tv.stepInto(c, Description[ST, H, S]("Inhale Assertion")))((σ1, c1) =>
          Q(σ1, c1))

      case ast.Exhale(a, _) =>
        val pve = AssertionViolated(stmt)
        consume(σ, FullPerms(), a, pve, c, tv)((σ1, _, _, c1) =>
          Q(σ1, c1))

      case call @ ast.Call(lhs, meth, args) =>
        val BigAnd = ast.utils.collections.BigAnd(meth.expressionFactory) _
        val pve = InvocationFailed(call)

        evals(σ, args.args, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Arguments")))((tArgs, c1) => {
          val (rdVar, rdVarConstraints) = freshReadVar("$CallRd", c1.currentRdPerms)
          val c2 = (c1.setConsumeExactReads(false)
                      .setCurrentRdPerms(ReadPerms(rdVar)))
          val insγ = Γ(meth.signature.parameters.variables.zip(tArgs))
          val pre = BigAnd(meth.signature.precondition, Predef.identity)
          assume(rdVarConstraints, c2)
          consume(σ \ insγ, FullPerms(), pre, pve, c2, tv.stepInto(c2, ScopeChangingDescription[ST, H, S]("Consume Precondition")))((σ1, _, _, c3) => {
            val outsγ = Γ(meth.signature.results.map(v => (v, fresh(v))).toMap)
            val σ2 = σ1 \+ outsγ \ (g = σ.h)
            val post = BigAnd(meth.signature.postcondition, Predef.identity)
            produce(σ2, fresh, FullPerms(), post, pve, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Produce Postcondition")))((σ3, c4) => {
              val lhsγ = Γ(lhs.zip(meth.signature.results)
                              .map(p => (p._1, σ3.γ(p._2))).toMap)
              val c5 = (c4.setConsumeExactReads(true)
                          .setCurrentRdPerms(c2.currentRdPerms))
              Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ), c5)})})})

      case ast.New(v, dt) =>
        assert(v.dataType == dt, "Expected same data type for lhs and rhs.")
        Q(σ \+ (v, fresh(v)), c)

      case fold @ ast.Fold(semper.sil.ast.expressions.terms.PredicateLocation(eRcvr, predicate), ePerm) =>
        val pve = FoldFailed(fold)
        eval(σ, eRcvr, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tRcvr, c1) =>
          if (decider.assert(tRcvr !== Null()))
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              decider.isValidFraction(tPerm, ePerm) match {
                case None =>
                  val insγ = Γ((predicate.factory.thisVar -> tRcvr))
                  val c2a = c2.setCurrentRdPerms(PredicateRdPerms())
                  consume(σ \ insγ, tPerm, predicate.expression, pve, c2a, tv.stepInto(c2a, ScopeChangingDescription[ST, H, S]("Consume Predicate Body")))((σ1, snap, dcs, c3) => {
                    val ncs = dcs.map{_ match {
                      case fc: DirectFieldChunk => new NestedFieldChunk(fc)
                      case pc: DirectPredicateChunk => new NestedPredicateChunk(pc)
                    }}
                    /* Producing Access is unfortunately not an option here
                    * since the following would fail due to productions
                    * starting in an empty heap:
                    *
                    *   predicate V { acc(x) }
                    *
                    *   function f(a: int): int
                    *	   requires rd(x)
                    * 	 { x + a }
                    *
                    *   method test(a: int)
                    *     requires ... ensures ...
                    *   { fold acc(V, f(a)) }
                    *
                    * Fold would fail since acc(V, f(a)) is produced in an
                    * empty and thus f(a) fails due to missing permissions to
                    * read x.
                    *
                    * TODO: Use heap merge function here!
                    */
                    val (h, t, tPerm1) = decider.getChunk[DirectPredicateChunk](σ1.h, tRcvr, predicate.name) match {
                      case Some(pc) => (σ1.h - pc, pc.snap.convert(sorts.Snap) === snap.convert(sorts.Snap), pc.perm + tPerm)
                      case None => (σ1.h, True(), tPerm)}
                    val c3a = c3.setCurrentRdPerms(c2.currentRdPerms)
                    assume(t, c3a)
                    val h1 = (h + DirectPredicateChunk(tRcvr, predicate.name, snap, tPerm1, ncs)
                                + H(ncs))
                    Q(σ \ h1, c3a)})
                case Some(reason) =>
                  Failure[C, ST, H, S, TV](pve dueTo reason, c2, tv)})
          else
            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))

      case unfold @ ast.Unfold(
              acc @ ast.PredicateAccessPredicate(ast.PredicateLocation(eRcvr, pred), ePerm)) =>

        val pve = UnfoldFailed(unfold)
        eval(σ, eRcvr, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tRcvr, c1) =>
          if (decider.assert(tRcvr !== Null()))
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              decider.isValidFraction(tPerm, ePerm) match {
                case None =>
                  val insγ = Γ((pred.factory.thisVar -> tRcvr))
                  consume(σ, FullPerms(), acc, pve, c2, tv.stepInto(c2, Description[ST, H, S]("Consume Predicate Chunk")))((σ1, snap, _, c3) => {
                    val c4 = c3.setCurrentRdPerms(PredicateRdPerms())
                    produce(σ1 \ insγ, s => snap.convert(s), tPerm, pred.expression, pve, c4, tv.stepInto(c4, ScopeChangingDescription[ST, H, S]("Produce Predicate Body")))((σ2, c5) => {
                      val c5 = c4.setCurrentRdPerms(c3.currentRdPerms)
                      Q(σ2 \ σ.γ, c5)})})
                case Some(reason) =>
                  Failure[C, ST, H, S, TV](pve dueTo reason, c2, tv)})
          else
            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))
		}

		executed
	}
}