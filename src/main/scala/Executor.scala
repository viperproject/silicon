package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.errors.{Internal, InhaleFailed, LoopInvariantNotPreserved,
    LoopInvariantNotEstablished, WhileFailed, AssignmentFailed, ExhaleFailed, PreconditionInCallFalse, FoldFailed,
    UnfoldFailed, AssertFailed}
import semper.sil.verifier.reasons.{InsufficientPermission, NonPositivePermission, ReceiverNull, AssertionFalse}
import interfaces.{Executor, Evaluator, Producer, Consumer, VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapCompressor}
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{PredicateChunkIdentifier, FieldChunkIdentifier, DirectFieldChunk, DirectPredicateChunk, SymbolConvert,
    DirectChunk, NestedFieldChunk, NestedPredicateChunk}
import reporting.DefaultContext
import heap.QuantifiedChunkHelper
import state.terms.perms.IsPositive

trait DefaultExecutor[ST <: Store[ST],
                      H <: Heap[H],
											PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
		extends Executor[ast.CFGBlock, ST, H, S, DefaultContext]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext]
									  with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext]
									  with Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext]
									  with Brancher[ST, H, S, DefaultContext] =>

  private type C = DefaultContext
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.{fresh, assume, inScope}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshARP

  protected val heapCompressor: HeapCompressor[ST, H, S]
  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config

  private def follow(σ: S, edge: ast.CFGEdge, c: C)
                    (Q: (S, C) => VerificationResult)
                    : VerificationResult = {

    edge match {
      case ce: sil.ast.ConditionalEdge =>
        eval(σ, ce.cond, Internal(ce.cond), c)((tCond, c1) =>
        /* TODO: Use FollowEdge instead of IfBranching */
          branch(σ, tCond, c1,
            (c2: C) => exec(σ, ce.dest, c2)(Q),
            (c2: C) => Success()))

      case ue: sil.ast.UnconditionalEdge => exec(σ, ue.dest, c)(Q)
    }
  }

  private def follows(σ: S, edges: Seq[ast.CFGEdge], c: C)
                     (Q: (S, C) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(σ, c)
    } else
      follows2(σ, edges, c)(Q)
  }

  private def follows2(σ: S, edges: Seq[ast.CFGEdge], c: C)
                      (Q: (S, C) => VerificationResult)
                      : VerificationResult = {

    if (edges.isEmpty) {
      Success()
    } else {
      follow(σ, edges.head, c)(Q) && follows2(σ, edges.tail, c)(Q)
    }
  }

  private def leave(σ: S, block: ast.CFGBlock, c: C)
                   (Q: (S, C) => VerificationResult)
                   : VerificationResult = {

    follows(σ, block.succs, c)(Q)
  }

  def exec(σ: S, block: ast.CFGBlock, c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult = {

    block match {
      case block @ sil.ast.StatementBlock(stmt, _) =>
        exec(σ, stmt, c)((σ1, c1) =>
          leave(σ1, block, c1)(Q))

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
        val wvs = lb.writtenVars
        val γBody = Γ(wvs.foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))
        val σBody = Σ(γBody, Ø, σ.g) /* Use the old-state of the surrounding block as the old-state of the loop. */

        (inScope {
          /* Verify loop body (including well-formedness check) */
          decider.prover.logComment("Verify loop body")
          produce(σBody, fresh,  FullPerm(), invAndGuard, WhileFailed(loopStmt), c)((σ1, c1) =>
          /* TODO: Detect potential contradictions between path conditions from loop guard and invariant.
           *       Should no longer be necessary once we have an on-demand handling of merging and
           *       false-checking.
           */
            if (decider.checkSmoke())
              Success() /* TODO: Mark branch as dead? */
            else
              exec(σ1, lb.body, c1)((σ2, c2) =>
                consumes(σ2,  FullPerm(), lb.invs, e => LoopInvariantNotPreserved(e), c2)((σ3, _, _, c3) =>
                  Success())))}
            &&
          inScope {
            /* Verify call-site */
            decider.prover.logComment("Establish loop invariant")
            consumes(σ,  FullPerm(), lb.invs, e => LoopInvariantNotEstablished(e), c)((σ1, _, _, c1) => {
              val σ2 = σ1 \ γBody
              decider.prover.logComment("Continue after loop")
              produce(σ2, fresh,  FullPerm(), invAndNotGuard, WhileFailed(loopStmt), c1)((σ3, c2) =>
              /* TODO: Detect potential contradictions between path conditions from loop guard and invariant.
               *       Should no longer be necessary once we have an on-demand handling of merging and
               *       false-checking.
               */
                if (decider.checkSmoke())
                  Success() /* TODO: Mark branch as dead? */
                else
                  leave(σ3, lb, c2)(Q))})})

        case frp @ sil.ast.ConstrainingBlock(vars, body, succ) =>
          val arps = vars map σ.γ.apply
          val c1 = c.setConstrainable(arps, true)
          exec(σ, body, c1)((σ1, c2) =>
            leave(σ1, frp, c2.setConstrainable(arps, false))(Q))
    }
  }

  private def exec(σ: S, stmts: Seq[ast.Statement], c: C)
                  (Q: (S, C) => VerificationResult)
                  : VerificationResult =

    if(stmts.nonEmpty)
      exec(σ, stmts.head, c)((σ1, c1) =>
        exec(σ1, stmts.tail, c1)(Q))
    else
      Q(σ, c)

  private def exec(σ: S, stmt: ast.Statement, c: C)
                  (Q: (S, C) => VerificationResult)
                  : VerificationResult = {

    actualExec(σ, stmt, c)((σ1, c1) => {
      Q(σ1, c1)
    })
  }

	private def actualExec(σ: S, stmt: ast.Statement, c: C)
			    (Q: (S, C) => VerificationResult)
          : VerificationResult = {

    /* For debugging-purposes only */
    stmt match {
      case _: sil.ast.Seqn =>
      case _ =>
        logger.debug(s"\nEXECUTE ${stmt.pos}: $stmt")
        logger.debug(stateFormatter.format(σ))
        decider.prover.logComment("[exec]")
        decider.prover.logComment(stmt.toString)
    }

		val executed = stmt match {
      case sil.ast.Seqn(stmts) =>
        exec(σ, stmts, c)(Q)

      case ass @ ast.Assignment(v, rhs) =>
        eval(σ, rhs, AssignmentFailed(ass), c)((tRhs, c1) =>
          Q(σ \+ (v, tRhs), c1))

      /* Assignment for a field that contains quantified chunks */
      case ass@ast.FieldWrite(fl@ast.FieldAccess(eRcvr, field), rhs) if quantifiedChunkHelper.isQuantifiedFor(σ.h, field.name) =>
//        val ch = quantifiedChunkHelper.getQuantifiedChunk(σ.h, field.name).get // TODO: Slightly inefficient, since it repeats the work of isQuantifiedFor
        val pve = AssignmentFailed(ass)
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          eval(σ, rhs, pve, c1)((tRhs, c2) => {
            decider.assume(NullTrigger(tRcvr))
            decider.assert(σ, tRcvr !== Null()){
              case false =>
                Failure[ST, H, S](pve dueTo ReceiverNull(fl))
              case true =>
                val (ch, optIdx) = quantifiedChunkHelper.transformElement(tRcvr, field.name, tRhs, FullPerm()/*, Nil*/)
//                println(s"  ch = $ch")
                // TODO: !!!!!! qch.permission needs to instantiate quantified index variables with the index
                //       !!!!!! used in the current receiver (i.e., with ch.quantifiedVars)
                val perms = quantifiedChunkHelper.permission(σ.h, FieldChunkIdentifier(tRcvr, field.name), optIdx.toSeq)
//                println(s"  perms = $perms")
                decider.assert(σ, AtLeast(perms, FullPerm())){
                  case false =>
                    Failure[ST, H, S](pve dueTo InsufficientPermission(fl))
                  case true =>
//                    val ch = quantifiedChunkHelper.transformElement(tRcvr, field.name, tRhs, FullPerm())
//                    quantifiedChunkHelper.consume(σ, σ.h, ch, pve, fl, c2)(h =>
                    quantifiedChunkHelper.consume(σ, σ.h, tRcvr, field, ch.perm, optIdx.toSeq, pve, fl, c2)(h =>
                      Q((σ \ h) \+ ch, c2))}}}))

      case ass @ ast.FieldWrite(fl @ ast.FieldAccess(eRcvr, field), rhs) =>
        val pve = AssignmentFailed(ass)
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          decider.assert(σ, tRcvr !== Null()){
            case true =>
              eval(σ, rhs, pve, c1)((tRhs, c2) => {
                val id = FieldChunkIdentifier(tRcvr, field.name)
                decider.withChunk[DirectChunk](σ, σ.h, id, FullPerm(), fl, pve, c2)(fc =>
                  Q(σ \- fc \+ DirectFieldChunk(tRcvr, field.name, tRhs, fc.perm), c2))})
            case false =>
              Failure[ST, H, S](pve dueTo ReceiverNull(fl))})

      case ast.New(v, fields) =>
        val t = fresh(v)
        assume(t !== Null())
        val newh = H(fields.map(f => DirectFieldChunk(t, f.name, fresh(f.name, toSort(f.typ)), FullPerm())))
        val σ1 = σ \+ (v, t) \+ newh
        val refs = state.utils.getDirectlyReachableReferencesState[ST, H, S](σ1) - t
        assume(state.terms.utils.BigAnd(refs map (_ !== t)))
        Q(σ1, c)

      case ast.Fresh(vars) =>
        val (arps, arpConstraints) =
          vars.map(v => (v, freshARP()))
              .map{case (variable, (value, constrain)) => ((variable, value), constrain)}
              .unzip
        val γ1 = Γ(σ.γ.values ++ arps)
          /* It is crucial that the (var -> term) mappings in arps override
           * already existing bindings for the same vars when they are added
           * (via ++).
           */
        assume(toSet(arpConstraints))
        Q(σ \ γ1, c)

      case inhale @ ast.Inhale(a) =>
        produce(σ, fresh, FullPerm(), a, InhaleFailed(inhale), c)((σ1, c1) =>
          Q(σ1, c1))

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(σ, FullPerm(), a, pve, c)((σ1, _, _, c1) =>
          Q(σ1, c1))

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.True =>
            heapCompressor.compress(σ, σ.h)
            Q(σ, c)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.False =>
            decider.tryOrFail[(S, C)](σ)((σ1, QS, QF) => {
            if (decider.checkSmoke())
                QS(σ1, c)
            else
                QF(Failure[ST, H, S](pve dueTo AssertionFalse(a)))
            })(_ => Success())

          case _ =>
            if (config.disableSubsumption()) {
              val r =
                consume(σ, FullPerm(), a, pve, c)((σ1, _, _, c1) =>
                  Success())
              r && Q(σ,c)
            } else
              consume(σ, FullPerm(), a, pve, c)((σ1, _, _, c1) =>
                Q(σ, c1))
        }

      case call @ ast.Call(methodName, eArgs, lhs) =>
        val meth = c.program.findMethod(methodName)
        val pve = PreconditionInCallFalse(call)
          /* TODO: Used to be MethodCallFailed. Is also passed on to producing the postcondition, during which
           *       it is passed on to calls to eval, but it could also be thrown by produce itself (probably
           *       only while checking well-formedness).
           */

        evals(σ, eArgs, pve, c)((tArgs, c1) => {
          val insγ = Γ(meth.formalArgs.map(_.localVar).zip(tArgs))
          val pre = ast.utils.BigAnd(meth.pres)
          consume(σ \ insγ, FullPerm(), pre, pve, c1)((σ1, _, _, c3) => {
            val outs = meth.formalReturns.map(_.localVar)
            val outsγ = Γ(outs.map(v => (v, fresh(v))).toMap)
            val σ2 = σ1 \+ outsγ \ (g = σ.h)
            val post = ast.utils.BigAnd(meth.posts)
            produce(σ2, fresh, FullPerm(), post, pve, c3)((σ3, c4) => {
              val lhsγ = Γ(lhs.zip(outs)
                              .map(p => (p._1, σ3.γ(p._2))).toMap)
              Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ), c4)})})})

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = c.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
            evalp(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsPositive(tPerm)){
                case true =>
                  val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                  consume(σ \ insγ, tPerm, predicate.body, pve, c2)((σ1, snap, dcs, c3) => {
                    val ncs = dcs.map {
                      case fc: DirectFieldChunk => new NestedFieldChunk(fc)
                      case pc: DirectPredicateChunk => new NestedPredicateChunk(pc)
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
                    val (h, t, tPerm1) = decider.getChunk[DirectPredicateChunk](σ, σ1.h, id) match {
                      case Some(pc) => (σ1.h - pc, pc.snap.convert(sorts.Snap) === snap.convert(sorts.Snap), pc.perm + tPerm)
                      case None => (σ1.h, True(), tPerm)}
                    assume(t)
                    val h1 = h + DirectPredicateChunk(predicate.name, tArgs, snap, tPerm1, ncs) + H(ncs)
                    Q(σ \ h1, c3)})
                case false =>
                  Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm))}))

      case unfold @ ast.Unfold(acc @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = c.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
            evalp(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsPositive(tPerm)){
                case true =>
                  val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                  consume(σ, FullPerm(), acc, pve, c2)((σ1, snap, _, c3) =>
                    produce(σ1 \ insγ, s => snap.convert(s), tPerm, predicate.body, pve, c3)((σ2, c4) =>
                      Q(σ2 \ σ.γ, c4)))
                case false =>
                  Failure[ST, H, S](pve dueTo NonPositivePermission(ePerm))}))

      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: sil.ast.Goto
           | _: sil.ast.If
           | _: sil.ast.Label
           | _: sil.ast.Seqn
           | _: sil.ast.Constraining
           | _: sil.ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")
		}

		executed
	}
}
