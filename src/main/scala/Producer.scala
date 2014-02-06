package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import sil.ast.utility.Permissions.isConditional
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapMerger}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import interfaces.reporting.TraceView
import interfaces.state.factoryUtils.Ø
import state.terms._
import semper.silicon.state._
import reporting.{DefaultContext, Producing, ImplBranching, IfBranching, Bookkeeper}
import semper.silicon.state.DirectFieldChunk
import semper.silicon.state.terms.*
import semper.silicon.state.DirectPredicateChunk
import semper.silicon.reporting.DefaultContext
import semper.silicon.heap.QuantifiedChunkHelper
import interfaces.state.StoreFactory
import state.terms._
import state.terms.implicits._
import semper.sil.ast.{LocalVar, LocalVarDecl}


trait DefaultProducer[
ST <: Store[ST],
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
      // TODO: merge for conditional chunks
        val (mh, mts) = merge(Ø, h)
        assume(mts)
        Q(σ \ mh, c1)
    })

  def produces(σ: S,
               sf: Sort => Term,
               p: P,
               φs: Seq[ast.Expression],
               pvef: ast.Expression => PartialVerificationError,
               c: C,
               tv: TV)
              (Q: (S, C) => VerificationResult)
  : VerificationResult = {
    //println(φs)
    if (φs.isEmpty)
      Q(σ, c)
    else
      produce(σ, sf, p, φs.head, pvef(φs.head), c, tv)((σ1, c1) =>
        produces(σ1, sf, p, φs.tail, pvef, c1, tv)(Q))   }

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

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) if quantifiedChunkHelper.isQuantifiedFor(σ.h, field.name) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val ch = QuantifiedChunk(field.name, s, TermPerm(Ite(*() === tRcvr, pNettoGain, NoPerm())))
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)
          })
        })

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            // TODO: make merge work here again
            val (mh, mts) = merge(σ.h, H(ch :: Nil))
            assume(mts)
            Q(mh, c2)
          })
        })

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), gain) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) =>
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(sorts.Snap)
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            if (!isConditional(gain)) assume(NoPerm() < pGain)
            // TODO: make merge work again
            val (mh, mts) = merge(σ.h, H(ch :: Nil))
            decider.prover.logComment("assuming predicate " + predicate.name)
            assume(mts)
            Q(mh, c2)
          }))

      // e.g. requires forall y:Ref :: y in xs ==> acc(y.f, write)
      case fa@ ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, f), gain))) => {
        decider.prover.logComment("Producing set access predicate " + fa)

          val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
          val γVars = Γ(((vars map (v => LocalVar(v.name)(v.typ))) zip tVars).asInstanceOf[Iterable[(ast.Variable, Term)]] /* won't let me do it without a cast */)

          eval(σ \+ γVars, cond, pve, c, tv)((tCond, c1) =>
            eval(σ \+ γVars, eRcvr, pve, c1, tv)((tRcvr, c2) => {
              decider.prover.logComment("End produce set access predicate " + fa)
              evalp(σ \+ γVars, gain, pve, c2, tv)((pGain, c3) => {
                // TODO: why does sf not work? This might introduce an incompleteness somewhere - ask Malte
                val s = /* sf(sorts.Arrow(sorts.Ref, toSort(f.typ))) */ decider.fresh(sorts.Arrow(sorts.Ref, toSort(f.typ)))
                val app = DomainFApp(Function(s.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
                val ch = quantifiedChunkHelper.transformInExhale(tRcvr, f, app, pGain * p, tCond)
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
