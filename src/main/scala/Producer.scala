package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter,
    HeapMerger, PermissionChunk}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult, Failure}
import interfaces.decider.Decider
import interfaces.reporting.TraceView
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{DirectFieldChunk, DirectPredicateChunk, TypeConverter, DirectChunk}
import reporting.{DefaultContext, Producing, ImplBranching, IfBranching, Bookkeeper}

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

	protected val typeConverter: TypeConverter
	import typeConverter.toSort

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
  import stateUtils.freshARP

	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val bookkeeper: Bookkeeper
	protected val config: Config

	private var snapshotCacheFrames: Stack[Map[Term, (Term, Term)]] = Stack()
	private var snapshotCache: Map[Term, (Term, Term)] = Map()

	def produce(σ: S,
              sf: Sort => Term,
              p: P,
              φ: ast.Expression,
              pve: PartialVerificationError,
              c: C,
              tv: TV)
			       (Q: (S, C) => VerificationResult)
             : VerificationResult =

    produce2(σ, sf, p, φ, pve, c, tv)((h, c1) => {
      val (mh, mts) = merge(Ø, h)
      assume(mts, c1)
      Q(σ \ mh, c1)})

  def produces(σ: S,
               sf: Sort => Term,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, C) => VerificationResult)
              : VerificationResult =

    if (φs.isEmpty)
      Q(σ, c)
    else
      produce(σ, sf, p, φs.head, pvef(φs.head), c, tv)((σ1, c1) =>
        produces(σ1, sf, p, φs.tail, pvef, c1, tv)(Q))

  private def produce2(σ: S,
                       sf: Sort => Term,
                       p: P,
                       φ: ast.Expression,
                       pve: PartialVerificationError,
                       c: C,
                       tv: TV)
                       (Q: (H, C) => VerificationResult)
                      : VerificationResult = {

    val tv1 = tv.stepInto(c, Producing[ST, H, S](σ, p, φ))

    internalProduce(σ, sf, p, φ, pve, c, tv1)((h, c1) => {
      tv1.currentStep.σPost = σ \ h
      Q(h, c1)
    })
  }

	private def internalProduce(σ: S,
                              sf: Sort => Term,
                              p: P,
                              φ: ast.Expression,
                              pve: PartialVerificationError,
                              c: C,
                              tv: TV)
			                       (Q: (H, C) => VerificationResult)
                             : VerificationResult = {

		logger.debug("\nPRODUCE " + φ.toString)
		logger.debug(stateFormatter.format(σ))

		val produced = φ match {
      case ast.And(a0, a1) if !φ.isPure =>
        val s0 = fresh(sorts.Snap)
        val s1 = fresh(sorts.Snap)
        val tSnapEq = SnapEq(sf(sorts.Snap), Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

				assume(tSnapEq, c)
        produce2(σ, sf0, p, a0, pve, c, tv)((h1, c1) =>
          produce2(σ \ h1, sf1, p, a1, pve, c1, tv)((h2, c2) =>
          Q(h2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
				eval(σ, e0, pve, c, tv)((t0, c1) =>
					branch(t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
						(c2: C, tv1: TV) => produce2(σ, sf, p, a0, pve, c2, tv1)(Q),
						(c2: C, tv1: TV) => Q(σ.h, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(t0, c1, tv, IfBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => produce2(σ, sf, p, a1, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => produce2(σ, sf, p, a2, pve, c2, tv1)(Q)))

      case ast.FieldAccessPredicate(ast.FieldLocation(eRcvr, field), gain) =>
//        producePermissions[DirectFieldChunk](σ, sf, p, fa, gain, DirectFieldChunk, toSort(field.typ), pve, c, tv)((h, ch, c1) =>
        producePermissions(σ, sf, p, eRcvr, field.name, gain, DirectFieldChunk, toSort(field.typ), pve, c, tv)((h, ch, c1) =>
          Q(h, c1))

      case ast.PredicateAccessPredicate(ast.PredicateLocation(eRcvr, pred), gain) =>
        val dpc =
          (rcvr: Term, id: String, snap: Term, p: P) =>
            DirectPredicateChunk(rcvr, id, snap, p)

        producePermissions(σ, sf, p, eRcvr, pred.name, gain, dpc, sorts.Snap, pve, c, tv)((h, _, c1) =>
          Q(h, c1))

//      case qe @ ast.Quantified(
//                  ast.Exists(),
//                  qvar,
//                  ast.BinaryOp(
//                    _: ast.And,
//                    rdStarConstraints,
//                    pe @ ast.FieldAccessPredicate(
//                            ast.FieldLocation(eRcvr, field),
//                            _)))
//            if toSort(qvar.dataType) == sorts.Perms =>
//
//        val witness = qvar
//        val (tWitness, _) = freshPermVar(witness.name)
//        val σ1 = σ \+ (witness, tWitness)
//        eval(σ1, rdStarConstraints, pve, c, tv)((tRdStarConstraints, c1) => {
//          assume(tRdStarConstraints, c1)
//          produce2(σ1, sf, p, pe, pve, c1, tv)((h1, c2) =>
//            Q(h1, c2))})

			/* Any regular expressions, i.e. boolean and arithmetic. */
			case _ =>
				eval(σ, φ, pve, c, tv)((t, c1) => {
					assume(t, c1)
          Q(σ.h, c1)})
		}

		produced
	}

  /* TODO: Replace parameters sf and sort by s: Sort and apply sf(sort) prior to calling the method. */
  private def producePermissions(σ: S,
                                 sf: Sort => Term,
                                 p: P,
                                 eRcvr: ast.Expression,
                                 id: String,
                                 gain: ast.Expression,
                                 chConstructor: (Term, String, Term, P) => DirectChunk,
                                 sort: Sort,
                                 pve: PartialVerificationError,
                                 c: C,
                                 tv: TV)
                                (Q: (H, DirectChunk, C) => VerificationResult)
                                : VerificationResult = {

    eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
      assume(tRcvr !== Null(), c1)
      evalp(σ, gain, pve, c1, tv)((pGain, c3) => {
        val s = sf(sort)
        val (pNettoGain: P, tFr: Set[Term]) = (pGain * p, Set[Term](True()))
        val ch = chConstructor(tRcvr, id, s, pNettoGain)

        assume(NoPerm() < pGain, c3)
        val (mh, mts) = merge(σ.h, H(ch :: Nil))
        assume(mts ++ tFr, c3)
        Q(mh, ch, c3)})})
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
