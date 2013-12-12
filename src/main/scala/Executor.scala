package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{LetWandFailed, Internal, LoopInvariantNotPreserved, UnfoldFailed, AssertFailed,
    PackageFailed, ApplyFailed, LoopInvariantNotEstablished, WhileFailed, AssignmentFailed, ExhaleFailed,
    PreconditionInCallFalse, FoldFailed}
import sil.verifier.reasons.{MagicWandChunkNotFound, NonPositivePermission, ReceiverNull, AssertionFalse}
import interfaces.{Executor, Evaluator, Producer, Consumer, VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapMerger}
import interfaces.reporting.TraceView
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{MagicWandChunk, PredicateChunkIdentifier, FieldChunkIdentifier, DirectFieldChunk, DirectPredicateChunk,
    SymbolConvert, DirectChunk, NestedFieldChunk, NestedPredicateChunk}
import reporting.{DefaultContext, Executing, IfBranching, Description, BranchingDescriptionStep,
    ScopeChangingDescription}
import supporters.MagicWandSupporter

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

  protected implicit val manifestH: Manifest[H]

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

  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C]

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
        decider.prover.logComment(s"loop at ${lb.pos}")

        /* TODO: We should avoid roundtripping, i.e., parsing a SIL file into an AST,
         *       which is then converted into a CFG, from which we then compute an
         *       AST again.
         */
        val loopStmt = lb.toAst.asInstanceOf[ast.While]
        val inv = ast.utils.BigAnd(lb.invs, Predef.identity, lb.pos)
        val invAndGuard = ast.And(inv, lb.cond)(inv.pos, inv.info)
        val notGuard = ast.Not(lb.cond)(lb.cond.pos, lb.cond.info)
        val invAndNotGuard = ast.And(inv, notGuard)(inv.pos, inv.info)

        /* Havoc local variables that are assigned to in the loop body but
         * that have been declared outside of it, i.e. before the loop.
         */
        val wvs = lb.writtenVars filterNot (_.typ == ast.types.Wand)
          /* TODO: BUG: Variables declared by LetWand show up in this list, but shouldn't! */

        val γBody = Γ(wvs.foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))
        val σBody = Σ(γBody, Ø, σ.g) /* Use the old-state of the surrounding block as the old-state of the loop. */

        (inScope {
          /* Verify loop body (including well-formedness check) */
          decider.prover.logComment("Verify loop body")
          val (c0, tv0) = tv.splitOffLocally(c, BranchingDescriptionStep[ST, H, S]("Loop Invariant Preservation"))
          produce(σBody, fresh,  FullPerm(), invAndGuard, WhileFailed(loopStmt), c0, tv0)((σ1, c1) =>
            /* TODO: Detect potential contradictions between path conditions from loop guard and invariant.
             *       Should no longer be necessary once we have an on-demand handling of merging and
             *       false-checking.
             */
            if (decider.assert(False()))
              Success[C, ST, H, S](c1) /* TODO: Mark branch as dead? */
            else
              exec(σ1, lb.body, c1, tv0)((σ2, c2) =>
              consumes(σ2,  FullPerm(), lb.invs, e => LoopInvariantNotPreserved(e), c2, tv0)((σ3, _, _, c3) =>
                  Success[C, ST, H, S](c3))))}
            &&
          inScope {
            /* Verify call-site */
            decider.prover.logComment("Establish loop invariant")
            val tv0 = tv.stepInto(c, Description[ST, H, S]("Loop Invariant Establishment"))
            val c0 = c
            consumes(σ,  FullPerm(), lb.invs, e => LoopInvariantNotEstablished(e), c0, tv0)((σ1, _, _, c1) => {
              val σ2 = σ1 \ γBody
              decider.prover.logComment("Continue after loop")
              produce(σ2, fresh,  FullPerm(), invAndNotGuard, WhileFailed(loopStmt), c1, tv0)((σ3, c2) =>
              /* TODO: Detect potential contradictions between path conditions from loop guard and invariant.
               *       Should no longer be necessary once we have an on-demand handling of merging and
               *       false-checking.
               */
                if (decider.assert(False()))
                  Success[C, ST, H, S](c2) /* TODO: Mark branch as dead? */
                else
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
        v.typ match {
          case ast.types.Wand =>
            assert(rhs.isInstanceOf[ast.MagicWand], s"Expected magic wand but found $rhs (${rhs.getClass.getName}})")
            val wand = rhs.asInstanceOf[ast.MagicWand]
            /* TODO: Inefficient! Create ChunkIdentifier w/o creating a chunk. */
            val id = magicWandSupporter.createChunk(σ.γ, σ.h, wand).id
            decider.getChunk[MagicWandChunk[H]](σ.h, id) match {
              case Some(ch) =>
                Q(σ \+ (v, WandChunkRef(ch)), c)
              case None =>
                Failure[C, ST, H, S, TV](LetWandFailed(ass) dueTo MagicWandChunkNotFound(wand), c, tv)}

          case _ =>
            eval(σ, rhs, AssignmentFailed(ass), c, tv)((tRhs, c1) =>
              Q(σ \+ (v, tRhs), c1))
        }

      case ass @ ast.FieldWrite(fl @ ast.FieldAccess(eRcvr, field), rhs) =>
        val pve = AssignmentFailed(ass)
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

          case _ =>
            if (config.disableSubsumption()) {
              val r =
                consume(σ, FullPerm(), a, pve, c.copy(reinterpretWand = false), tv)((σ1, _, _, c1) =>
                  Success[C, ST, H, S](c1))
              r && Q(σ, c)
            } else
              consume(σ, FullPerm(), a, pve, c.copy(reinterpretWand = false), tv)((σ1, _, _, c1) =>
                Q(σ, c1.copy(reinterpretWand = true)))
        }

      case call @ ast.Call(meth, eArgs, lhs) =>
        val pve = PreconditionInCallFalse(call)
          /* TODO: Used to be MethodCallFailed. Is also passed on to producing the postcondition, during which
           *       it is passed on to calls to eval, but it could also be thrown by produce itself (probably
           *       only while checking well-formedness).
           */

        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Arguments")))((tArgs, c1) => {
          val insγ = Γ(meth.formalArgs.map(_.localVar).zip(tArgs))
          val pre = ast.utils.BigAnd(meth.pres)
          consume(σ \ insγ, FullPerm(), pre, pve, c1, tv.stepInto(c1, ScopeChangingDescription[ST, H, S]("Consume Precondition")))((σ1, _, _, c3) => {
            val outs = meth.formalReturns.map(_.localVar)
            val outsγ = Γ(outs.map(v => (v, fresh(v))).toMap)
            val σ2 = σ1 \+ outsγ \ (g = σ.h)
            val post = ast.utils.BigAnd(meth.posts)
            produce(σ2, fresh, FullPerm(), post, pve, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Produce Postcondition")))((σ3, c4) => {
              val lhsγ = Γ(lhs.zip(outs)
                              .map(p => (p._1, σ3.γ(p._2))).toMap)
              Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ), c4)})})})

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm)) =>
        val pve = FoldFailed(fold)
        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tArgs, c1) =>
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              if (decider.isPositive(tPerm)) {
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                consume(σ \ insγ, tPerm, predicate.body, pve, c2, tv.stepInto(c2, ScopeChangingDescription[ST, H, S]("Consume Predicate Body")))((σ1, snap, dcs, c3) => {
                  val ncs = dcs flatMap {
                    case fc: DirectFieldChunk => Some(new NestedFieldChunk(fc))
                    case pc: DirectPredicateChunk => Some(new NestedPredicateChunk(pc))
                    case _: MagicWandChunk[H] => None
                  }
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
                  assume(t)
                  val h1 = h + DirectPredicateChunk(predicate.name, tArgs, snap, tPerm1, ncs) + H(ncs)
                  Q(σ \ h1, c3)})}
              else
                Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c2, tv)))

      case unfold @ ast.Unfold(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), ePerm)) =>
        val pve = UnfoldFailed(unfold)
        evals(σ, eArgs, pve, c, tv.stepInto(c, Description[ST, H, S]("Evaluate Receiver")))((tArgs, c1) =>
            evalp(σ, ePerm, pve, c1, tv.stepInto(c1, Description[ST, H, S]("Evaluate Permissions")))((tPerm, c2) =>
              if (decider.isPositive(tPerm)) {
                val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                consume(σ, FullPerm(), acc, pve, c2, tv.stepInto(c2, Description[ST, H, S]("Consume Predicate Chunk")))((σ1, snap, _, c3) => {
                  produce(σ1 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3, tv.stepInto(c3, ScopeChangingDescription[ST, H, S]("Produce Predicate Body")))((σ2, c4) => {
                    Q(σ2 \ σ.γ, c4)})})}
              else
                Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(ePerm), c2, tv)))

      case pckg @ ast.Package(wand) =>
        val pve = PackageFailed(pckg)
        val σ0 = Σ(σ.γ, Ø, σ.g)
        val c0 = c.copy(poldHeap = Some(σ.h))
        produce(σ0, fresh, FullPerm(), wand.left, pve, c0, tv.stepInto(c, Description[ST, H, S]("Produce wand lhs")))((σLhs, c1) => {
          val c2 = c1.copy(reserveHeap = Some(σ.h), givenHeap = Some(σLhs.h), reinterpretWand = false)
          val rhs = injectExhalingExp(wand.right)
          consume(σLhs, FullPerm(), rhs, pve, c2, tv.stepInto(c2, Description[ST, H, S]("Consume wand rhs")))((σ1, _, _, c3) => {
            val σ2 = σ \ c3.reserveHeap.get
            val c4 = c3.copy(reserveHeap = None, poldHeap = None, givenHeap = None, reinterpretWand = true)
            /* Producing the wand is not an option because we need to pass in σ.h */
            val ch = magicWandSupporter.createChunk(σ2.γ, σ.h, wand)
            Q(σ2 \+ ch, c4)})})

      case apply @ ast.Apply(e) =>
        val pve = ApplyFailed(apply)
        val (wand, wandValues) = magicWandSupporter.resolveWand(σ, e)
        /* TODO: Since resolveWand might already know the chunk it would be faster if we
         *       removed it from the heap directly instead of consuming the wand.
         */
        consume(σ \+ Γ(wandValues), FullPerm(), wand, pve, c.copy(reinterpretWand = false), tv)((σ1, _, chs, c1) => {
          assert(chs.size == 1 && chs(0).isInstanceOf[MagicWandChunk[H]], "Unexpected list of consumed chunks: $chs")
          val ch = chs(0).asInstanceOf[MagicWandChunk[H]]
          /* TODO: The given heap is not σ.h, but rather the consumed portion only. However,
           *       using σ.h should not be a problem as long as the heap that is used as
           *       the given-heap while checking self-framingness of the wand is the heap
           *       described by the left-hand side.
           */
          val c1a = c1.copy(poldHeap = Some(ch.hPO), givenHeap = Some(σ.h), reinterpretWand = true)
          consume(σ1, FullPerm(), wand.left, pve, c1a, tv)((σ2, _, _, c2) =>
            produce(σ2, fresh, FullPerm(), wand.right, pve, c2, tv)((σ3, c3) => {
              val c4 = c3.copy(poldHeap = None, givenHeap = None)
              Q(σ3 \ σ.γ, c4)}))}) /* TODO: Remove wandValues from γ instead of using old σ.γ */

      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: sil.ast.Goto
           | _: sil.ast.If
           | _: sil.ast.Label
           | _: sil.ast.Seqn
           | _: sil.ast.FreshReadPerm
           | _: sil.ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")
		}

		executed
	}

  private def injectExhalingExp(exp: ast.Expression): ast.Expression = {
    /* TODO: Only works if exp is a direct nesting of ghost operations, i.e., not something such as
     *       folding acc(x.P) in (acc(x.Q) &&  applying ...)
     *       This structure is currently not guaranteed by consistency checks.
     */

    exp.transform {
      case gop: ast.GhostOperation if (   !gop.body.isInstanceOf[ast.GhostOperation]
                                       && !gop.body.isPure) =>

        val exh = ast.Exhaling(gop.body)(gop.body.pos, gop.body.info)

        gop match {
          case e: ast.Folding => e.copy(body = exh)(e.pos, e.info)
          case e: ast.Unfolding => e.copy(body = exh)(e.pos, e.info)
          case e: ast.Applying => e.copy(body = exh)(e.pos, e.info)
          case _ => sys.error(s"Unexpected ghost operation $gop (${gop.getClass.getName})")
        }
    }()
  }
}
