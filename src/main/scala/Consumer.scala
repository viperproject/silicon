package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import semper.sil.verifier.reasons.{InsufficientPermission, NonPositivePermission, ReceiverNull, AssertionFalse}
import sil.ast.utility.Permissions.isConditional
import interfaces.state.{Store, Heap, PathConditions, State, StateFormatter, StateFactory, ChunkIdentifier}
import interfaces.{Consumer, Evaluator, VerificationResult, Failure}
import interfaces.reporting.TraceView
import interfaces.decider.Decider
import state.{FieldChunkIdentifier, SymbolConvert, DirectChunk, DirectFieldChunk, DirectPredicateChunk, DirectQuantifiedChunk}
import semper.silicon.state.terms._
import reporting.{DefaultContext, Consuming, ImplBranching, IfBranching, Bookkeeper}
import semper.silicon.heap.HeapManager
import semper.sil.ast.{LocationAccess, LocalVar}
import semper.sil.verifier.reasons.NonPositivePermission
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.terms.*
import semper.silicon.state.DirectPredicateChunk
import semper.silicon.interfaces.Failure
import semper.silicon.state.DirectQuantifiedChunk
import semper.silicon.state.terms.False
import semper.silicon.state.terms.TermPerm
import semper.silicon.reporting.DefaultContext
import semper.silicon.state.terms.Combine
import semper.silicon.PermissionsConsumptionResult
import semper.silicon.state.terms.Var
import semper.silicon.state.terms.WildcardPerm
import semper.sil.verifier.reasons.AssertionFalse

trait DefaultConsumer[ST <: Store[ST], H <: Heap[H],
											PC <: PathConditions[PC], S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
									  with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.assume

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._


  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshARP

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

	protected val chunkFinder: ChunkFinder[P, ST, H, S, C, TV]
	import chunkFinder.withChunk

  protected val heapManager: HeapManager[ST, H, PC, S, C, TV]

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

  /*
   * ATTENTION: The DirectChunks passed to the continuation correspond to the
   * chunks as they existed when the consume took place. More specifically,
   * the amount of permissions that come with these chunks is NOT the amount
   * that has been consumed, but the amount that was found in the heap.
   */
	def consume(σ: S, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
             (Q: (S, Term, List[DirectChunk], C) => VerificationResult)
             : VerificationResult =

    consume2(σ, σ.h, p, φ, pve, c, tv)((h1, t, dcs, c1) =>
      Q(σ \ h1, t, dcs, c1))

  def consumes(σ: S,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
              : VerificationResult =

    consumes2(σ, σ.h, p, φs, Nil, Nil, pvef, c, tv)(Q)

  private def consumes2(σ: S, h: H, p: P, φs: Seq[ast.Expression], ts: List[Term], dcs: List[DirectChunk], pvef: ast.Expression => PartialVerificationError, c: C, tv: TV)
                       (Q: (S, List[Term], List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

    if (φs.isEmpty)
      Q(σ \ h, ts.reverse, dcs.reverse, c)
    else
      consume(σ, h, p, φs.head, pvef(φs.head), c, tv)((h1, t, dcs1, c1) =>
        consumes2(σ, h1, p, φs.tail, t :: ts, dcs1 ::: dcs, pvef, c1, tv)(Q))

	protected def consume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                 (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                       : VerificationResult =

		consume2(σ, h, p, φ, pve, c, tv)(Q)

  protected def consume2(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                  (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                        : VerificationResult = {

    val tv1 = tv.stepInto(c, Consuming[ST, H, S](σ, h, p, φ))

    internalConsume(σ, h, p, φ, pve, c, tv1)((h1, s1, dcs, c1) => {
      tv1.currentStep.σPost = σ \ h1
      Q(h1, s1, dcs, c1)
    })
  }

	private def internalConsume(σ: S, h: H, p: P, φ: ast.Expression, pve: PartialVerificationError, c: C, tv: TV)
			                  (Q: (H, Term, List[DirectChunk], C) => VerificationResult)
                        : VerificationResult = {

		decider.prover.logComment("\nCONSUME " + φ.toString)
    decider.prover.logComment(stateFormatter.format(σ))
    decider.prover.logComment("h = " + stateFormatter.format(h))

		val consumed = φ match {
      case ast.InhaleExhaleExp(_, a1) =>
        consume(σ, h, p, a1, pve, c, tv)(Q)

      case ast.And(a1, a2) if !φ.isPure =>
				consume(σ, h, p, a1, pve, c, tv)((h1, s1, dcs1, c1) =>
					consume(σ, h1, p, a2, pve, c1, tv)((h2, s2, dcs2, c2) =>
						Q(h2, Combine(s1.convert(sorts.Snap), s2.convert(sorts.Snap)), dcs1 ::: dcs2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => consume(σ, h, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(h, Unit, Nil, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => consume(σ, h, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => consume(σ, h, p, a2, pve, c2, tv1)(Q)))


      // TODO: generalize for arbitrary condition and receiver
      case ast.Forall(vars, triggers, ast.Implies(cond, a@ast.FieldAccessPredicate(ast.FieldAccess(ast.SeqIndex(seq, idx), field), loss))) => {
        decider.prover.logComment("CONSUMING SEQ FORALL")
        val tVars = vars map (v => decider.fresh(v.name, toSort(v.typ)))
        val γVars = Γ(((vars map (v => LocalVar(v.name)(v.typ))) zip tVars).asInstanceOf[Iterable[(ast.Variable, Term)]] /* won't let me do it without a cast */)
        eval(σ \+ γVars, cond, pve, c, tv)((tCond, c1) =>
        eval(σ \+ γVars, seq, pve, c, tv)((tSeq, c2) =>
          evalp(σ, loss, pve, c1, tv) ((tPerm, c3) => {
          val k = decider.fresh("blabu", sorts.Ref)
          val i = decider.fresh("i", sorts.Int)
          // TODO: decide where the rewriting should be done - here or in the heapmanager
          // TODO: we dont need cond rewriting anymore
          val rewrittenCond = tCond match {
            case SeqIn(SeqRanged(a,b),c) => (And(And(AtLeast(i,a),Less(i, b)), SeqAt(tSeq,i)===k))
            case _ => sys.error("cannot handle such a condition " + cond)
          }
          val rewrittenGain = tCond match {
             case SeqIn(SeqRanged(a,b),c) => PermTimes(tPerm, TermPerm(MultisetCount(*(), MultisetFromSeq(SeqDrop(SeqTake(tSeq,b),a)))))
             case _ => sys.error("I cannot work with condition of the form " + cond)
          }

            if(decider.inScope({
            assume(rewrittenCond.replace(*(), k))
            decider.assert(False())
          })) {
            // guard is false, we do not need to do anything
            Q(h, Unit, Nil, c3)
          } else {
            // we may safely assume the ""guard""
            assume(rewrittenCond.replace(*(), k))

            heapManager.consumePermissions(h, h.empty + DirectQuantifiedChunk(field.name, null, rewrittenGain), k, field, pve, a.loc, c2, tv) ((h1, t) => {
              Q(h1, t, Nil, c3)
            })
          }
        })))
      }

      // e.g. ensures forall y:Ref :: y in xs ==> acc(y.f, write)
      case ast.Forall(vars, triggers, ast.Implies(ast.SetContains(elem, set), a@ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), loss))) => {
        eval(σ, set, pve, c, tv)((tSet, c1) =>
          evalp(σ, loss, pve, c1, tv)((tPerm, c2) => {
            val k = decider.fresh("myblub", sorts.Ref)
            // quick workaround: check if it is false
            // TODO: this is unsound!!! Imagine the set to be empty, then we assume false!
            if (decider.inScope({
            	assume(SetIn(k, tSet))
            	decider.assert(False())
        	})) {
        		// guard is false, we do not need to do anything
        		Q(h, Unit, Nil, c2)
        	}
        	else
        	 {
        	// we may safely assume it
        	assume(SetIn(k, tSet))
            heapManager.consumePermissions(h, h.empty + DirectQuantifiedChunk(field.name, null /* value of the chunk */, TermPerm(Ite(SetIn(*(), tSet), tPerm, NoPerm()))), k, field, pve, a.loc , c2, tv)((h1,t) =>  {
                /* TODO: is this correct? */
                Q(h1, t, Nil, c2)
              })
            }
          })
        )
      }

      // pure forall e.g. ensures forall y:Ref :: y in xs ==> y.f > 0
      case ast.Forall(vars, triggers, ast.Implies(cond, body)) if(body.isPure &&  /* only if there are conditional chunks on the heap */ σ.h.values.exists(_.isInstanceOf[DirectQuantifiedChunk])) => {
        decider.inScope({
          decider.prover.logComment("CONSUMING PURE FORALL")

          val tVars = vars map (v => decider.fresh(v.name, toSort(v.typ)))
          val γVars = Γ(((vars map (v => LocalVar(v.name)(v.typ))) zip tVars).asInstanceOf[Iterable[(ast.Variable, Term)]] /* won't let me do it without a cast */)
          // restriction: the permission is constant and we can evaluate it here
          eval(σ \+ γVars, cond, pve, c, tv)((tCond, c1) => {
            val rewrittenCond = heapManager.rewriteGuard(tCond)

            if(decider.inScope({
            	assume(rewrittenCond)
            	decider.assert(False())
            })) {
            	Q(h, Unit, Nil, c1)
            } else {
            	assume(rewrittenCond)
            	eval(σ \+ γVars, body, pve, c1, tv)((tBody, c2) => {
              		if (decider.assert(tBody)) {
                	Q(h, Unit /* not really correct */, Nil, c2)
              	} else {
               		 Failure[C, ST, H, S, TV](pve dueTo AssertionFalse(φ), c, tv)
              	}
            })
            }
            
          })
        })
      }

      /* Field and predicate access predicates */
      case ast.AccessPredicate(locacc@ast.FieldAccess(eRcvr, field), perm) if (heapManager.isQuantifiedFor(h, field.name)) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
            heapManager.consumePermissions(h, h.empty + DirectQuantifiedChunk(locacc.loc.name, null, TermPerm(Ite(Eq(*(), tRcvr), tPerm, NoPerm()))), tRcvr, field, pve, locacc, c2, tv)((h2: H, t) =>
              Q(h2, t, Nil, c2)
            )))

      case ast.AccessPredicate(locacc, perm) =>
        withChunkIdentifier(σ, locacc, true, pve, c, tv)((id, c1) =>
              evalp(σ, perm, pve, c1, tv)((tPerm, c2) =>
                if (decider.isPositive(tPerm, !isConditional(perm)))
                  consumePermissions(σ, h, id, p * tPerm, locacc, pve, c2, tv)((h1, ch, c3, results) =>
                    ch match {
                      case fc: DirectFieldChunk =>
                          val snap = fc.value.convert(sorts.Snap)
                          Q(h1, snap, fc :: Nil, c3)

                      case pc: DirectPredicateChunk =>
                        val h2 =
                          if (results.consumedCompletely)
                            pc.nested.foldLeft(h1){case (ha, nc) => ha - nc}
                          else
                            h1
                        Q(h2, pc.snap, pc :: Nil, c3)})
                else
                  Failure[C, ST, H, S, TV](pve dueTo NonPositivePermission(perm), c2, tv)))

			/* Any regular Expressions, i.e. boolean and arithmetic.
			 * IMPORTANT: The expression is evaluated in the initial heap (σ.h) and
			 * not in the partially consumed heap (h).
			 */
      case _ =>
        // assert(σ, h, φ, m, ExpressionMightEvaluateToFalse, Q)
        eval(σ, φ, pve, c, tv)((t, c) => {
          decider.prover.logComment("asserting: " + φ)
          if (decider.assert(t)) {
            assume(t)
            Q(h, Unit, Nil, c)
          } else
            Failure[C, ST, H, S, TV](pve dueTo AssertionFalse(φ), c, tv) })

		}

		consumed
	}

  private def consumePermissions(σ: S,
                                 h: H,
                                 id: ChunkIdentifier,
                                 pLoss: P,
                                 // tRcvr: Term,
                                 locacc: ast.LocationAccess,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q:     (H, DirectChunk, C, PermissionsConsumptionResult)
                                     => VerificationResult)
                                :VerificationResult = {

    /* TODO: assert that pLoss > 0 */

    if (consumeExactRead(pLoss, c)) {
      withChunk[DirectChunk](h, id, pLoss, locacc, pve, c, tv)(ch => {
        if (decider.assertNoAccess(ch.perm - pLoss)) {
          Q(h - ch, ch, c, PermissionsConsumptionResult(true))}
        else
          Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    } else {
      withChunk[DirectChunk](h, id, locacc, pve, c, tv)(ch => {
        assume(pLoss < ch.perm)
        Q(h - ch + (ch - pLoss), ch, c, PermissionsConsumptionResult(false))})
    }
  }

  private def consumeExactRead(fp: P, c: C): Boolean = fp match {
    case TermPerm(v: Var) => !c.constrainableARPs.contains(v)
    case _: TermPerm => true
    case _: WildcardPerm => false
    case PermPlus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermMinus(t0, t1) => consumeExactRead(t0, c) || consumeExactRead(t1, c)
    case PermTimes(t0, t1) => consumeExactRead(t0, c) && consumeExactRead(t1, c)
    case IntPermTimes(_, t1) => consumeExactRead(t1, c)
    case _ => true
  }
}

private case class PermissionsConsumptionResult(consumedCompletely: Boolean)
