package semper
package silicon

import com.weiglewilczek.slf4s.Logging
import scala.collection.immutable.Stack
import sil.verifier.PartialVerificationError
import sil.ast.utility.Permissions.isConditional
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapMerger}
import interfaces.{Success, Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import interfaces.reporting.TraceView
import interfaces.state.factoryUtils.Ã˜
import state.terms._
import state.{DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import reporting.{DefaultContext, Producing, ImplBranching, IfBranching, Bookkeeper}
import supporters.MagicWandSupporter

trait DefaultProducer[
                      ST <: Store[ST],
                      H <: Heap[H],
											PC <: PathConditions[PC],
                      S <: State[ST, H, S],
											TV <: TraceView[TV, ST, H, S]]
		extends Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV] with HasLocalState
		{ this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
                    with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
									  with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

	protected val decider: Decider[P, ST, H, PC, S, C]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val heapMerger: HeapMerger[H]
	import heapMerger.merge

	protected val symbolConverter: SymbolConvert
	import symbolConverter.toSort

  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

	private var snapshotCacheFrames: Stack[Map[Term, (Term, Term)]] = Stack()
	private var snapshotCache: Map[Term, (Term, Term)] = Map()

	def produce(Ïƒ: S,
              sf: Sort => Term,
              p: P,
              Ï†: ast.Expression,
              pve: PartialVerificationError,
              c: C,
              tv: TV)
			       (Q: (S, C) => VerificationResult)
             : VerificationResult =

    produce2(Ïƒ, sf, p, Ï†, pve, c, tv)((h, c1) => {
      val (mh, mts) = merge(Ã˜, h)
      assume(mts)
      Q(Ïƒ \ mh, c1)})

  def produces(Ïƒ: S,
               sf: Sort => Term,
               p: P,
               Ï†s: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, C) => VerificationResult)
              : VerificationResult =

    if (Ï†s.isEmpty)
      Q(Ïƒ, c)
    else
      produce(Ïƒ, sf, p, Ï†s.head, pvef(Ï†s.head), c, tv)((Ïƒ1, c1) =>
        produces(Ïƒ1, sf, p, Ï†s.tail, pvef, c1, tv)(Q))

  private def produce2(Ïƒ: S,
                       sf: Sort => Term,
                       p: P,
                       Ï†: ast.Expression,
                       pve: PartialVerificationError,
                       c: C,
                       tv: TV)
                       (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    val tv1 = tv.stepInto(c, Producing[ST, H, S](Ïƒ, p, Ï†))

    internalProduce(Ïƒ, sf, p, Ï†, pve, c, tv1)((h, c1) => {
      tv1.currentStep.ÏƒPost = Ïƒ \ h
      Q(h, c1)
    })
  }

	private def internalProduce(Ïƒ: S,
                              sf: Sort => Term,
                              p: P,
                              Ï†: ast.Expression,
                              pve: PartialVerificationError,
                              c: C,
                              tv: TV)
			                       (Q: (H, C) => VerificationResult)
                             : VerificationResult = {

    logger.debug(s"\nPRODUCE ${Ï†.pos}: ${Ï†}")
		logger.debug(stateFormatter.format(Ïƒ))

		val produced = Ï† match {
      case ast.InhaleExhaleExp(a0, _) =>
        produce2(Ïƒ, sf, p, a0, pve, c, tv)(Q)

      case ast.And(a0, a1) if !Ï†.isPure =>
        val s0 = fresh(sorts.Snap)
        val s1 = fresh(sorts.Snap)
        val tSnapEq = Eq(sf(sorts.Snap), Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

				assume(tSnapEq)
        produce2(Ïƒ, sf0, p, a0, pve, c, tv)((h1, c1) =>
          produce2(Ïƒ \ h1, sf1, p, a1, pve, c1, tv)((h2, c2) =>
          Q(h2, c2)))

      case ast.Implies(e0, a0) if !Ï†.isPure =>
				eval(Ïƒ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => produce2(Ïƒ, sf, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(Ïƒ.h, c2)))

      case ast.Ite(e0, a1, a2) if !Ï†.isPure =>
        eval(Ïƒ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c1, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => produce2(Ïƒ, sf, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => produce2(Ïƒ, sf, p, a2, pve, c2, tv1)(Q)))

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(Ïƒ, eRcvr, pve, c, tv)((tRcvr, c1) =>
          /* Assuming receiver non-null might contradict current path conditions
           * and we would like to detect that as early as possible.
           * We could try to assert false after the assumption, but it seems likely
           * that 'tRcvr === Null()' syntactically occurs in the path conditions if
           * it is true. Hence, we assert it here, which (should) syntactically look
           * for the term before calling Z3.
           */
          if (decider.assert(tRcvr === Null())) /* TODO: Benchmark performance impact */
            Success[C, ST, H, S](c1)
          else {
            assume(tRcvr !== Null())
            evalp(Ïƒ, gain, pve, c1, tv)((pGain, c2) => {
              val s = sf(toSort(field.typ))
              val pNettoGain = pGain * p
              val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
              if (!isConditional(gain)) assume(NoPerm() < pGain)
              val (mh, mts) = merge(Ïƒ.h, H(ch :: Nil))
              assume(mts)
              Q(mh, c2)})})

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), gain) =>
        evals(Ïƒ, eArgs, pve, c, tv)((tArgs, c1) =>
          evalp(Ïƒ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(sorts.Snap)
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            val (mh, mts) = merge(Ïƒ.h, H(ch :: Nil))
            assume(mts)
            Q(mh, c2)}))

      case wand: ast.MagicWand =>
        val ch = magicWandSupporter.createChunk(Ïƒ.Î³, Ïƒ.h, wand)
        Q(Ïƒ.h + ch, c)

			/* Any regular expressions, i.e. boolean and arithmetic. */
			case _ =>
				eval(Ïƒ, Ï†, pve, c, tv)((t, c1) => {
					assume(t)
          Q(Ïƒ.h, c1)})
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
