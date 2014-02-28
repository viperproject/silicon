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
import interfaces.state.factoryUtils.Ø
import state.terms._
import state.{DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import reporting.{DefaultContext, Producing, ImplBranching, IfBranching, Bookkeeper}
import supporters.MagicWandSupporter
import heap.QuantifiedChunkHelper

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S],
                      TV <: TraceView[TV, ST, H, S]]
                      extends Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV] with HasLocalState {
                      this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
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

  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C, TV]

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val magicWandSupporter: MagicWandSupporter[ST, H, PC, S, C]
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
        assume(mts)
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

    logger.debug(s"\nPRODUCE ${φ.pos}: ${φ}")
		logger.debug(stateFormatter.format(σ))

    val produced = φ match {
      case ast.InhaleExhaleExp(a0, _) =>
        produce2(σ, sf, p, a0, pve, c, tv)(Q)

      case ast.And(a0, a1) if !φ.isPure =>
        val s0 = fresh(sorts.Snap)
        val s1 = fresh(sorts.Snap)
        val tSnapEq = Eq(sf(sorts.Snap), Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

        assume(tSnapEq)
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

      /* Produce a field access if the heap is quantified for that field */
      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) if quantifiedChunkHelper.isQuantifiedFor(σ.h, field.name) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val ch = quantifiedChunkHelper.transformElement(tRcvr, field.name, s, pNettoGain)
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)
          })
        })

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) =>
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
            evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
              val s = sf(toSort(field.typ))
              val pNettoGain = pGain * p
              val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
              if (!isConditional(gain)) assume(NoPerm() < pGain)
              val (mh, mts) = merge(σ.h, H(ch :: Nil))
              assume(mts)
              Q(mh, c2)})})

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), gain) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) =>
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(sorts.Snap)
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            val (mh, mts) = merge(σ.h, H(ch :: Nil))
            assume(mts)
            Q(mh, c2)}))

      case wand: ast.MagicWand =>
        val ch = magicWandSupporter.createChunk(σ.γ, σ.h, wand)
        Q(σ.h + ch, c)

      /* Quantified field access predicate */
      case fa@ ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, f), gain))) => {
        decider.prover.logComment("Producing set access predicate " + fa)

          val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
          val γVars = Γ(((vars map (v => LocalVar(v.name)(v.typ))) zip tVars).asInstanceOf[Iterable[(ast.Variable, Term)]] /* won't let me do it without a cast */)

          eval(σ \+ γVars, cond, pve, c, tv)((tCond, c1) =>
            eval(σ \+ γVars, eRcvr, pve, c1, tv)((tRcvr, c2) => {
              decider.prover.logComment("End produce set access predicate " + fa)
              evalp(σ \+ γVars, gain, pve, c2, tv)((pGain, c3) => {
                // TODO https://bitbucket.org/semperproject/silicon/issue/59/create-sortwrappers-for-functions
                val s = /* sf(sorts.Arrow(sorts.Ref, toSort(f.typ))) */ decider.fresh(sorts.Arrow(sorts.Ref, toSort(f.typ)))
                val app = DomainFApp(Function(s.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
                val ch = quantifiedChunkHelper.transform(tRcvr, f, app, pGain * p, tCond)
                val v = Var("nonnull", sorts.Ref)
                val h = if(quantifiedChunkHelper.isQuantifiedFor(σ.h,f.name)) σ.h else quantifiedChunkHelper.quantifyChunksForField(σ.h, f.name)
                decider.assume(Quantification(Forall, List(v), Implies(Less(NoPerm(), ch.perm.replace(*(), v)), v !== Null()), List(Trigger(List(NullTrigger(v))))))
                Q(h+ch, c3)
              })
            })
          )
      }



      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        eval(σ, φ, pve, c, tv)((t, c1) => {
          //println(φ)
          //println("assuming " + t)
          assume(t)
          Q(σ.h, c1)
        })
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
