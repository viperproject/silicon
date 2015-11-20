/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import org.slf4s.Logging
import silver.ast
import silver.verifier.errors.{IfFailed, InhaleFailed, LoopInvariantNotPreserved,
    LoopInvariantNotEstablished, WhileFailed, AssignmentFailed, ExhaleFailed, PreconditionInCallFalse, FoldFailed,
    UnfoldFailed, AssertFailed, CallFailed}
import silver.verifier.reasons.{NegativePermission, ReceiverNull, AssertionFalse, InsufficientPermission}
import interfaces.{Executor, Evaluator, Producer, Consumer, VerificationResult, Failure, Success}
import interfaces.decider.Decider
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapCompressor}
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{FieldChunkIdentifier, DirectFieldChunk, SymbolConvert, DirectChunk, DefaultContext}
import state.terms.perms.IsNonNegative
import supporters.{Brancher, PredicateSupporter, QuantifiedChunkSupporter}

trait DefaultExecutor[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S]]
    extends Executor[ST, H, S, DefaultContext]
    { this: Logging with Evaluator[ST, H, S, DefaultContext]
                    with Consumer[DirectChunk, ST, H, S, DefaultContext]
                    with Producer[ST, H, S, DefaultContext]
                    with PredicateSupporter[ST, H, PC, S]
                    with Brancher[ST, H, S, DefaultContext] =>

  private type C = DefaultContext

  protected val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, assume, inScope}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val heapCompressor: HeapCompressor[ST, H, S, C]
  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S]
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config

  private def follow(σ: S, edge: ast.Edge, c: C)
                    (Q: (S, C) => VerificationResult)
                    : VerificationResult = {

    edge match {
      case ce: silver.ast.ConditionalEdge =>
        eval(σ, ce.cond, IfFailed(ce.cond), c)((tCond, c1) =>
        /* TODO: Use FollowEdge instead of IfBranching */
          branch(σ, tCond, c1,
            (c2: C) => exec(σ, ce.dest, c2)(Q),
            (c2: C) => Success()))

      case ue: silver.ast.UnconditionalEdge => exec(σ, ue.dest, c)(Q)
    }
  }

  private def follows(σ: S, edges: Seq[ast.Edge], c: C)
                     (Q: (S, C) => VerificationResult)
                     : VerificationResult = {

    if (edges.isEmpty) {
      Q(σ, c)
    } else
      follows2(σ, edges, c)(Q)
  }

  private def follows2(σ: S, edges: Seq[ast.Edge], c: C)
                      (Q: (S, C) => VerificationResult)
                      : VerificationResult = {

    if (edges.isEmpty) {
      Success()
    } else {
      follow(σ, edges.head, c)(Q) && follows2(σ, edges.tail, c)(Q)
    }
  }

  private def leave(σ: S, block: ast.Block, c: C)
                   (Q: (S, C) => VerificationResult)
                   : VerificationResult = {

    follows(σ, block.succs, c)(Q)
  }

  def exec(σ: S, block: ast.Block, c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult = {

    block match {
      case block @ silver.ast.StatementBlock(stmt, _) =>
        exec(σ, stmt, c)((σ1, c1) =>
          leave(σ1, block, c1)(Q))

      case lb: silver.ast.LoopBlock =>
        decider.prover.logComment(s"loop at ${lb.pos}")

        /* TODO: We should avoid roundtripping, i.e., parsing a SIL file into an AST,
         *       which is then converted into a CFG, from which we then compute an
         *       AST again.
         */
        val loopStmt = lb.toAst.asInstanceOf[ast.While]
        val notGuard = ast.Not(lb.cond)(lb.cond.pos, lb.cond.info)

        /* Havoc local variables that are assigned to in the loop body but
         * that have been declared outside of it, i.e. before the loop.
         */
        val wvs = (lb.locals.map(_.localVar) ++ lb.writtenVars).distinct
        val γBody = Γ(wvs.foldLeft(σ.γ.values)((map, v) => map.updated(v, fresh(v))))
        val σBody = Σ(γBody, Ø, σ.g) /* Use the old-state of the surrounding block as the old-state of the loop. */

        (inScope {
          /* Verify loop body (including well-formedness check) */
          decider.prover.logComment("Verify loop body")
          produces(σBody, fresh,  FullPerm(), lb.invs :+ lb.cond, _ => WhileFailed(loopStmt), c)((σ1, c1) =>
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
              produces(σ2, fresh,  FullPerm(), lb.invs :+ notGuard, _ => WhileFailed(loopStmt), c1)((σ3, c2) =>
              /* TODO: Detect potential contradictions between path conditions from loop guard and invariant.
               *       Should no longer be necessary once we have an on-demand handling of merging and
               *       false-checking.
               */
                if (decider.checkSmoke())
                  Success() /* TODO: Mark branch as dead? */
                else
                  leave(σ3, lb, c2)(Q))})})

        case frp @ silver.ast.ConstrainingBlock(vars, body, succ) =>
          val arps = vars map σ.γ.apply
          val c1 = c.setConstrainable(arps, true)
          exec(σ, body, c1)((σ1, c2) =>
            leave(σ1, frp, c2.setConstrainable(arps, false))(Q))
    }
  }

  def execs(σ: S, stmts: Seq[ast.Stmt], c: C)
           (Q: (S, C) => VerificationResult)
           : VerificationResult =

    if(stmts.nonEmpty)
      exec(σ, stmts.head, c)((σ1, c1) =>
        execs(σ1, stmts.tail, c1)(Q))
    else
      Q(σ, c)

  def exec(σ: S, stmt: ast.Stmt, c: C)
          (Q: (S, C) => VerificationResult)
          : VerificationResult = {

    /* For debugging-purposes only */
    stmt match {
      case _: silver.ast.Seqn =>
      case _ =>
        log.debug(s"\nEXECUTE ${stmt.pos}: $stmt")
        log.debug(stateFormatter.format(σ))
        decider.prover.logComment("[exec]")
        decider.prover.logComment(stmt.toString())
    }

    val executed = stmt match {
      case silver.ast.Seqn(stmts) =>
        execs(σ, stmts, c)(Q)

      case ass @ ast.LocalVarAssign(v, rhs) =>
        eval(σ, rhs, AssignmentFailed(ass), c)((tRhs, c1) =>
          Q(σ \+ (v, tRhs), c1))

      /* Assignment for a field that contains quantified chunks */
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
              if c.qpFields.contains(field) =>

        val pve = AssignmentFailed(ass)
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          eval(σ, rhs, pve, c1)((tRhs, c2) =>
            decider.assert(σ, tRcvr !== Null()){
              case false =>
                Failure[ST, H, S](pve dueTo ReceiverNull(fa))
              case true =>
                val hints = quantifiedChunkSupporter.extractHints(None, None, tRcvr)
                val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
                quantifiedChunkSupporter.splitSingleLocation(σ, σ.h, field, tRcvr, FullPerm(), chunkOrderHeuristics, c2) {
                  case Some((h1, _, _, c3)) =>
                    val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, tRcvr, tRhs)
                    optFvfDef.foreach(fvfDef => assume(fvfDef.domainDefinition :: fvfDef.valueDefinition :: Nil))
                    val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(tRcvr, field.name, fvf, FullPerm())
                    Q(σ \ h1 \+ ch, c3)
                  case None =>
                    Failure[ST, H, S](pve dueTo InsufficientPermission(fa))}}))

      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs) =>
        val pve = AssignmentFailed(ass)
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          decider.assert(σ, tRcvr !== Null()){
            case true =>
              eval(σ, rhs, pve, c1)((tRhs, c2) => {
                val id = FieldChunkIdentifier(tRcvr, field.name)
                decider.withChunk[DirectChunk](σ, σ.h, id, Some(FullPerm()), fa, pve, c2)((fc, c3) =>
                  Q(σ \- fc \+ DirectFieldChunk(tRcvr, field.name, tRhs, fc.perm), c3))})
            case false =>
              Failure[ST, H, S](pve dueTo ReceiverNull(fa))})

      case ast.NewStmt(v, fields) =>
        val tRcvr = fresh(v)
        assume(tRcvr !== Null())
        /* TODO: Verify similar to the code in DefaultProducer/ast.FieldAccessPredicate - unify */
        val newChunks = fields map (field => {
          val p = FullPerm()
          val s = fresh(field.name, toSort(field.typ))
          if (c.qpFields.contains(field)) {
            val (fvf, optFvfDef) = quantifiedChunkSupporter.createFieldValueFunction(field, tRcvr, s)
            optFvfDef.foreach(fvfDef => assume(fvfDef.domainDefinition :: fvfDef.valueDefinition :: Nil))
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(tRcvr, field.name, fvf, p)
          } else
            DirectFieldChunk(tRcvr, field.name, s, p)})
        val σ1 = σ \+ (v, tRcvr) \+ H(newChunks)
        val ts = state.utils.computeReferenceDisjointnesses[ST, H, S](σ1, tRcvr)
          /* Calling computeReferenceDisjointnesses with the updated state σ1 ensures that
           * tRcvr is constrained to be different from (ref-typed) fields of tRcvr to which
           * permissions have been gained.
           * Note that we do not constrain the (ref-typed) fields to be mutually disjoint.
           */
        assume(And(ts))
        Q(σ1, c)

      case ast.Fresh(vars) =>
        val (arps, arpConstraints) =
          vars.map(v => (v, decider.freshARP()))
              .map{case (variable, (value, constrain)) => ((variable, value), constrain)}
              .unzip
        val γ1 = Γ(σ.γ.values ++ arps)
          /* It is crucial that the (var -> term) mappings in arps override
           * already existing bindings for the same vars when they are added
           * (via ++).
           */
        assume(toSet(arpConstraints))
        Q(σ \ γ1, c)

      case inhale @ ast.Inhale(a) => a match {
        case _: ast.FalseLit =>
          /* We're done */
          Success()
        case _ =>
          produce(σ, fresh, FullPerm(), a, InhaleFailed(inhale), c)((σ1, c1) =>
            Q(σ1, c1))
      }

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(σ, FullPerm(), a, pve, c)((σ1, _, _, c1) =>
          Q(σ1, c1))

      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.TrueLit =>
            heapCompressor.compress(σ, σ.h, c)
            Q(σ, c)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.FalseLit =>
            decider.tryOrFail[S](σ, c)((σ1, c1, QS, QF) => {
              if (decider.checkSmoke())
                  QS(σ1, c1)
              else
                  QF(Failure[ST, H, S](pve dueTo AssertionFalse(a)))
              })((_, _) => Success())

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

      case call @ ast.MethodCall(methodName, eArgs, lhs) =>
        val meth = c.program.findMethod(methodName)
        val pvefCall = (_: ast.Exp) =>  CallFailed(call)
        val pvefPre = (_: ast.Exp) =>  PreconditionInCallFalse(call)
        evals(σ, eArgs, pvefCall, c)((tArgs, c1) => {
          val c2 = c1.copy(recordVisited = true)
          val insγ = Γ(meth.formalArgs.map(_.localVar).zip(tArgs))
          consumes(σ \ insγ, FullPerm(), meth.pres, pvefPre, c2)((σ1, _, _, c3) => {
            val outs = meth.formalReturns.map(_.localVar)
            val outsγ = Γ(outs.map(v => (v, fresh(v))).toMap)
            val σ2 = σ1 \+ outsγ \ (g = σ.h)
            produces(σ2, fresh, FullPerm(), meth.posts, pvefCall, c3)((σ3, c4) => {
              val lhsγ = Γ(lhs.zip(outs)
                              .map(p => (p._1, σ3.γ(p._2))).toMap)
              val c5 = c4.copy(recordVisited = c1.recordVisited)
              Q(σ3 \ (g = σ.g, γ = σ.γ + lhsγ), c5)})})})

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = c.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
            eval(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsNonNegative(tPerm)){
                case true =>
                  predicateSupporter.fold(σ, predicate, tArgs, tPerm, pve, c2)(Q)
                case false =>
                  Failure[ST, H, S](pve dueTo NegativePermission(ePerm))}))

      case unfold @ ast.Unfold(ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = c.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
            eval(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsNonNegative(tPerm)){
                case true =>
                  predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)(Q)
                case false =>
                  Failure[ST, H, S](pve dueTo NegativePermission(ePerm))}))

      /* These cases should not occur when working with the CFG-representation of the program. */
      case   _: silver.ast.Goto
           | _: silver.ast.If
           | _: silver.ast.Label
           | _: silver.ast.Seqn
           | _: silver.ast.Constraining
           | _: silver.ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")
    }

    executed
  }
}
