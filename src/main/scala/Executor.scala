package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{Internal, LoopInvariantNotPreserved, LoopInvariantNotEstablished,
    WhileFailed, AssignmentFailed, ExhaleFailed, PreconditionInCallFalse, FoldFailed,
    UnfoldFailed, AssertFailed}
import semper.sil.verifier.reasons.{InsufficientPermission, NonPositivePermission, ReceiverNull, AssertionFalse}
import interfaces.{Executor, Evaluator, Producer, Consumer, VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
    HeapMerger}
import interfaces.reporting.{/*Message,*/ TraceView}
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{PredicateChunkIdentifier, FieldChunkIdentifier, DirectFieldChunk, DirectPredicateChunk,
    SymbolConvert, DirectChunk, NestedFieldChunk, NestedPredicateChunk}
import reporting.{DefaultContext, Executing, IfBranching, Description, BranchingDescriptionStep,
    ScopeChangingDescription}

trait DefaultExecutor[ST <: Store[ST],
                      H <: Heap[H],
											PC <: PathConditions[PC],
                      S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Executor[ast.CFGBlock, ST, H, S, DefaultContext[ST, H, S], TV]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
									 with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.{fresh, assume, inScope}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val heapMerger: HeapMerger[H]
  import heapMerger.merge

	protected val chunkFinder: ChunkFinder[P, ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshARP

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config

  var program: ast.Program

  private def follow(σ: S, edge: ast.CFGEdge, c: C, tv: TV)
                    (Q: (S, C) => VerificationResult)
                    : VerificationResult = {

    edge match {
      case ce: sil.ast.ConditionalEdge =>
        eval(σ, ce.cond, Internal(ce.cond), c, tv)((tCond, c1) =>
        /* TODO: Use FollowEdge instead of IfBranching */
          branch(tCond, c1, tv, IfBranching[ST, H, S](ce.cond, tCond),
            (c2: C, tv1: TV) => exec(σ, ce.dest, c2, tv1)(Q),
            (c2: C, tv1: TV) => Success[C, ST, H, S](c2)))

      case ue: sil.ast.UnconditionalEdge => exec(σ, ue.dest, c, tv)(Q)
    }
  }

  private def follows(σ: S, edges: Seq[ast.CFGEdge], c: C, tv: TV)
                     (Q: (S, C) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(σ, c)
    } else
      follows2(σ, edges, c, tv)(Q)
  }

  private def follows2(σ: S, edges: Seq[ast.CFGEdge], c: C, tv: TV)
                      (Q: (S, C) => VerificationResult)
                      : VerificationResult = {

    if (edges.isEmpty) {
      Success[C, ST, H, S](c)
    } else {
      follow(σ, edges.head, c, tv)(Q) && follows2(σ, edges.tail, c, tv)(Q)
    }
  }

  private def leave(σ: S, block: ast.CFGBlock, c: C, tv: TV)
                   (Q: (S, C) => VerificationResult)
                   : VerificationResult = {

    follows(σ, block.succs, c, tv)(Q)
  }

  def exec(σ: S, block: ast.CFGBlock, c: C, tv: TV)
          (Q: (S, C) => VerificationResult)
          : VerificationResult = {

//    logger.debug("\n[exec] " + block.label)

    block match {
      case block @ sil.ast.StatementBlock(stmt, _) =>
        exec(σ, stmt, c, tv)((σ1, c1) =>
          leave(σ1, block, c1, tv)(Q))

      case lb: sil.ast.LoopBlock =>
        decider.prover.logComment(sil.ast.pretty.PrettyPrinter.pretty(lb.toAst))

        val inv = ast.utils.BigAnd(lb.invs, Predef.identity, lb.pos)
        val invAndGuard = ast.And(inv, lb.cond)(inv.pos, inv.info)
        val notGuard = ast.Not(lb.cond)(lb.cond.pos, lb.cond.info)
        val invAndNotGuard = ast.And(inv, notGuard)(inv.pos, inv.info)

        /* Havoc local variables that are assigned to in the loop body but
         * that have been declared outside of it, i.e. before the loop.
         */
        val wvs = lb.writtenVars
        val γBody = Γ(wvs.foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))
        val σBody = Σ(γBody, Ø, σ.g) /* Use the old-state of the surrounding block as the old-state of the loop. */

        (inScope {
          /* Verify loop body (including well-formedness check) */
          decider.prover.logComment("Verify loop body")
          val (c0, tv0) = tv.splitOffLocally(c, BranchingDescriptionStep[ST, H, S]("Loop Invariant Preservation"))
          produce(σBody, fresh,  FullPerm(), invAndGuard, WhileFailed(invAndGuard), c0, tv0)((σ1, c1) =>
            exec(σ1, lb.body, c1, tv0)((σ2, c2) =>
              consume(σ2,  FullPerm(), inv, LoopInvariantNotPreserved(inv), c2, tv0)((σ3, _, _, c3) =>
                Success[C, ST, H, S](c3))))}
            &&
          inScope {
            /* Verify call-site */
            decider.prover.logComment("Establish loop invariant")
            val tv0 = tv.stepInto(c, Description[ST, H, S]("Loop Invariant Establishment"))
            val c0 = c
            consume(σ,  FullPerm(), inv, LoopInvariantNotEstablished(inv), c0, tv0)((σ1, _, _, c1) => {
              val σ2 = σ1 \ γBody
              decider.prover.logComment("Continue after loop")
              produce(σ2, fresh,  FullPerm(), invAndNotGuard, WhileFailed(invAndNotGuard), c1, tv0)((σ3, c2) =>
                leave(σ3, lb, c2, tv)(Q))})})

        case frp @ sil.ast.FreshReadPermBlock(vars, body, succ) =>
          val (arps, arpConstraints) =
            vars.map(v => (v, freshARP()))
                .map{case (variable, (value, constrain)) => ((variable, value), constrain)}
                .unzip
          val γ1 = Γ(σ.γ.values ++ arps)
          val c1 = c.setConstrainable(arps map (_._2), true)
          assume(arpConstraints.toSet)
          exec(σ \ γ1, body, c1, tv)((σ1, c2) =>
            leave(σ1, frp, c2.setConstrainable(arps map (_._2), false), tv)(Q))
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

    /* For debugging-purposes only */
    stmt match {
      case _: sil.ast.Seqn =>
      case _ =>
        logger.debug("\nEXECUTE " + stmt.toString)
        logger.debug(stateFormatter.format(σ))
        decider.prover.logComment("")
        decider.prover.logComment(stmt.toString)
    }

		val executed = stmt match {
      case sil.ast.Seqn(stmts) =>
        exec(σ, stmts, c, tv)(Q)

      case ass @ ast.Assignment(v, rhs) =>
        eval(σ, rhs, AssignmentFailed(ass), c, tv)((tRhs, c1) =>
          Q(σ \+ (v, tRhs), c1))

      case ass @ ast.FieldWrite(fl @ ast.FieldAccess(eRcvr, field), rhs) =>
        val pve = AssignmentFailed(ass)
        val id = field.name
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          if (decider.assert(tRcvr !== Null()))
            eval(σ, rhs, pve, c1, tv)((tRhs, c2) => {
              val id = FieldChunkIdentifier(tRcvr, field.name)
              withChunk[DirectChunk](σ.h, id, FullPerm(), fl, pve, c2, tv)(fc =>
                Q(σ \- fc \+ DirectFieldChunk(tRcvr, field.name, tRhs, fc.perm), c2))})
          else
            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(fl), c1, tv))

      case ast.New(v) =>
        val t = fresh(v)
        assume(t !== Null())
        val newh = H(program.fields.map(f => DirectFieldChunk(t, f.name, fresh(f.name, toSort(f.typ)), FullPerm())))
        val σ1 = σ \+ (v, t) \+ newh
        val refs = state.utils.getDirectlyReachableReferencesState[ST, H, S](σ1) - t
        assume(state.terms.utils.BigAnd(refs map (_ !== t)))
        Q(σ1, c)

      case ast.Inhale(a) =>
        produce(σ, fresh, FullPerm(), a, Internal(stmt), c, tv.stepInto(c, Description[ST, H, S]("Inhale Assertion")))((σ1, c1) =>
          Q(σ1, c1))

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(σ, FullPerm(), a, pve, c, tv)((σ1, _, _, c1) =>
          Q(σ1, c1))

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.True =>
            val (mh, mts) = merge(Ø, σ.h)
            assume(mts)
            Q(σ \ mh, c)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.False =>
            if (decider.checkSmoke)
              Success[C, ST, H, S](c)
            else
              Failure[C, ST, H, S, TV](pve dueTo AssertionFalse(a), c, tv)

          case ast.AccessPredicate(locacc, perm) =>
            withChunkIdentifier(σ, locacc, true, pve, c, tv)((id, c1) =>
              evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
                if (decider.hasEnoughPermissionsGlobally(σ.h, id, tPerm))
                  Q(σ, c2)
                else
                  Failure[C, ST, H, S, TV](pve dueTo InsufficientPermission(locacc), c2, tv)))

          case _ =>
            if (config.disableSubsumption()) {
              val r =
                consume(σ, FullPerm(), a, pve, c, tv)((σ1, _, _, c1) =>
                  Success[C, ST, H, S](c1))
              r && Q(σ,c)
            } else
              consume(σ, FullPerm(), a, pve, c, tv)((σ1, _, _, c1) =>
                Q(σ, c1))
        }

      case call @ ast.Call(meth, eArgs, lhs) =>
        val pve = PreconditionInCallFalse(call)
          /* TODO: Used to be MethodCallFailed. Is also passed on to producing the postcondition, during which
           *       it is passed on to calls to eval, but it could also be thrown by produce itself (probably
           *       only while checking well-formedness).
           */

        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Arguments")))((tArgs, c1) => {
//          val (rdVar, rdVarConstraints) = freshReadVar("$CallRd", c1.currentRdPerms)
//          val c2 = (c1.setConsumeExactReads(false)
//                      .setCurrentRdPerms(ReadPerm(rdVar)))
          val insγ = Γ(meth.formalArgs.map(_.localVar).zip(tArgs))
          val pre = ast.utils.BigAnd(meth.pres)
//          assume(rdVarConstraints, c2)
          consume(σ \ insγ, FullPerm(), pre, pve, c1, tv.stepInto(c1, ScopeChangingDescription[ST, H, S]("Consume Precondition")))((σ1, _, _, c3) => {
            val outs = meth.formalReturns.map(_.localVar)
            val outsγ = Γ(outs.map(v => (v, fresh(v))).toMap)
            val σ2 = σ1 \+ outsγ \ (g = σ.h)
            val post = ast.utils.BigAnd(meth.posts)
            produce(σ2, fresh, FullPerm(), post, pve, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Produce Postcondition")))((σ3, c4) => {
              val lhsγ = Γ(lhs.zip(outs)
                              .map(p => (p._1, σ3.γ(p._2))).toMap)
//              val c5 = (c4.setConsumeExactReads(true)
//                          .setCurrentRdPerms(c2.currentRdPerms))
              Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ), c4)})})})

//      case ast.New(v, dt) =>
//        assert(v.dataType == dt, "Expected same data type for lhs and rhs.")
//        Q(σ \+ (v, fresh(v)), c)

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm)) =>
        val pve = FoldFailed(fold)
        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tArgs, c1) =>
//          if (decider.assert(tRcvr !== Null()))
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              if (decider.isPositive(tPerm)) {
//                  val insγ = Γ((ast.ThisLiteral()() -> tRcvr))
//                val insγ = Γ((predicate.formalArg.localVar -> tRcvr))
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
//                  val c2a = c2.setCurrentRdPerms(PredicateRdPerm())
                consume(σ \ insγ, tPerm, predicate.body, pve, c2, tv.stepInto(c2, ScopeChangingDescription[ST, H, S]("Consume Predicate Body")))((σ1, snap, dcs, c3) => {
                  val ncs = dcs.map{_ match {
                    case fc: DirectFieldChunk => new NestedFieldChunk(fc)
                    case pc: DirectPredicateChunk => new NestedPredicateChunk(pc)}}
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
                  val id = PredicateChunkIdentifier(predicate.name, tArgs)
                  val (h, t, tPerm1) = decider.getChunk[DirectPredicateChunk](σ1.h, id) match {
                    case Some(pc) => (σ1.h - pc, pc.snap.convert(sorts.Snap) === snap.convert(sorts.Snap), pc.perm + tPerm)
                    case None => (σ1.h, True(), tPerm)}
//                    val c3a = c3.setCurrentRdPerms(c2.currentRdPerms)
                  assume(t)
                  val h1 = (h + DirectPredicateChunk(predicate.name, tArgs, snap, tPerm1, ncs)
                              + H(ncs))
                  Q(σ \ h1, c3)})}
              else
                Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c2, tv)))
//          else
//            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))

      case unfold @ ast.Unfold(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm)) =>
        val pve = UnfoldFailed(unfold)
        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tArgs, c1) =>
//          if (decider.assert(tRcvr !== Null()))
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              if (decider.isPositive(tPerm)) {
//                  val insγ = Γ((ast.ThisLiteral()() -> tRcvr))
//                val insγ = Γ((predicate.formalArg.localVar -> tRcvr))
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                consume(σ, FullPerm(), acc, pve, c2, tv.stepInto(c2, Description[ST, H, S]("Consume Predicate Chunk")))((σ1, snap, _, c3) => {
//                    val c4 = c3.setCurrentRdPerms(PredicateRdPerm())
                  produce(σ1 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Produce Predicate Body")))((σ2, c4) => {
//                      val c5 = c4.setCurrentRdPerms(c3.currentRdPerms)
                    Q(σ2 \ σ.γ, c4)})})}
              else
                Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c2, tv)))
//          else
//            Failure[C, ST, H, S, TV](pve dueTo ReceiverNull(eRcvr), c1, tv))

      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: sil.ast.Goto
           | _: sil.ast.If
           | _: sil.ast.Label
           | _: sil.ast.Seqn
           | _: sil.ast.FreshReadPerm
           | _: sil.ast.While => sys.error("Not yet implemented (%s): %s".format(stmt.getClass.getName, stmt))
		}

		executed
	}
}
