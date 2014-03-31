package semper
package silicon

import scala.collection.immutable.Stack
import com.weiglewilczek.slf4s.Logging
import sil.verifier.PartialVerificationError
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter}
import interfaces.{Producer, Consumer, Evaluator, VerificationResult}
import interfaces.decider.Decider
import interfaces.reporting.TraceView
import state.terms._
import state.{DirectFieldChunk, DirectPredicateChunk, SymbolConvert, DirectChunk}
import reporting.{DefaultContext, Producing, ImplBranching, IfBranching, Bookkeeper}
import heap.QuantifiedChunkHelper
import sil.ast.LocalVar

trait DefaultProducer[ST <: Store[ST],
                      H <: Heap[H],
                      PC <: PathConditions[PC],
                      S <: State[ST, H, S],
                      TV <: TraceView[TV, ST, H, S]]
    extends Producer[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
        with HasLocalState
    { this: Logging with Evaluator[DefaultFractionalPermissions, ST, H, S, DefaultContext[ST, H, S], TV]
                    with Consumer[DefaultFractionalPermissions, DirectChunk, ST, H, S, DefaultContext[ST, H, S], TV]
                    with Brancher[ST, H, S, DefaultContext[ST, H, S], TV] =>

  private type C = DefaultContext[ST, H, S]
  private type P = DefaultFractionalPermissions

  protected val decider: Decider[P, ST, H, PC, S, C, TV]
  import decider.{fresh, assume}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val quantifiedChunkHelper: QuantifiedChunkHelper[ST, H, PC, S, C, TV]
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

    produce2(σ, sf, p, φ, pve, c, tv)((h, c1) =>
      Q(σ \ h, c1))

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

    if (!φ.isInstanceOf[ast.And]) {
      logger.debug(s"\nPRODUCE ${φ.pos}: $φ")
      logger.debug(stateFormatter.format(σ))
    }

    val produced = φ match {
      case ast.InhaleExhaleExp(a0, _) =>
        produce2(σ, sf, p, a0, pve, c, tv)(Q)

      case ast.And(a0, a1) if !φ.isPure =>
        val s0 = mkSnap(a0)
        val s1 = mkSnap(a1)
        val tSnapEq = Eq(sf(sorts.Snap), Combine(s0, s1))

        val sf0 = (sort: Sort) => s0.convert(sort)
        val sf1 = (sort: Sort) => s1.convert(sort)

        assume(tSnapEq)
        produce2(σ, sf0, p, a0, pve, c, tv)((h1, c1) =>
          produce2(σ \ h1, sf1, p, a1, pve, c1, tv)((h2, c2) =>
            Q(h2, c2)))

      case ast.Implies(e0, a0) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(σ, t0, c1, tv, ImplBranching[ST, H, S](e0, t0),
            (c2: C, tv1: TV) => produce2(σ, sf, p, a0, pve, c2, tv1)(Q),
            (c2: C, tv1: TV) => Q(σ.h, c2)))

      case ast.Ite(e0, a1, a2) if !φ.isPure =>
        eval(σ, e0, pve, c, tv)((t0, c1) =>
          branch(σ, t0, c1, tv, IfBranching[ST, H, S](e0, t0),
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
            assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)})})

      case ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), gain) =>
        eval(σ, eRcvr, pve, c, tv)((tRcvr, c1) => {
          assume(tRcvr !== Null())
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(toSort(field.typ))
            val pNettoGain = pGain * p
            val ch = DirectFieldChunk(tRcvr, field.name, s, pNettoGain)
            assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)})})

      case ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicate), gain) =>
        evals(σ, eArgs, pve, c, tv)((tArgs, c1) =>
          evalp(σ, gain, pve, c1, tv)((pGain, c2) => {
            val s = sf(getOptimalSnapshotSort(predicate.body)._1)
            val pNettoGain = pGain * p
            val ch = DirectPredicateChunk(predicate.name, tArgs, s, pNettoGain)
            assume(NoPerm() < pGain)
            Q(σ.h + ch, c2)}))

      /* Quantified field access predicate */
      case fa@ ast.Forall(vars, triggers, ast.Implies(cond, ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, f), gain))) =>
        decider.prover.logComment("Producing set access predicate " + fa)

          val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
          val γVars = Γ(((vars map (v => LocalVar(v.name)(v.typ))) zip tVars).asInstanceOf[Iterable[(ast.Variable, Term)]] /* won't let me do it without a cast */)

          eval(σ \+ γVars, cond, pve, c, tv)((tCond, c1) =>
            eval(σ \+ γVars, eRcvr, pve, c1, tv)((tRcvr, c2) => {
              decider.prover.logComment("End produce set access predicate " + fa)
              evalp(σ \+ γVars, gain, pve, c2, tv)((pGain, c3) => {
                /* TODO https://bitbucket.org/semperproject/silicon/issue/59/create-sortwrappers-for-functions */
//                println("\n[produce/forall]")
                val s = decider.fresh(sorts.Arrow(sorts.Ref, toSort(f.typ)))
//                println(s"  s = $s")
//                val sREAL = sf(sorts.Arrow(sorts.Ref, toSort(f.typ)))
//                val sREAL = sf(toSort(f.typ))
//                println(s"  sREAL = $sREAL  (${sREAL.getClass.getName}})")
                val value = DomainFApp(Function(s.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
//                val value = sREAL // DomainFApp(Function(s.id, sorts.Arrow(sorts.Ref, toSort(f.typ))), List(*()))
//                println(s"  value = $value")
//                println(s"  pGain * p = ${pGain * p}")
//                println(s"  tCond * p = $tCond")
                val ch = quantifiedChunkHelper.transform(tRcvr, f, value, pGain * p, tCond)
//                println(s"  ch = $ch")
                val v = Var("nonnull", sorts.Ref)
//                val auxQuant =
//                  Quantification(
//                    Forall,
//                    List(v),
//                    Implies(
//                      Less(NoPerm(), ch.perm.replace(*(), v)),
//                      v !== Null()),
//                    List(Trigger(List(NullTrigger(v)))))
//                println(s"  auxQuant = $auxQuant")
//                decider.assume(auxQuant)
                val h =
                  if(quantifiedChunkHelper.isQuantifiedFor(σ.h,f.name)) σ.h
                  else quantifiedChunkHelper.quantifyChunksForField(σ.h, f.name)
                Q(h + ch, c3)})}))

      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        eval(σ, φ, pve, c, tv)((t, c1) => {
          assume(t)
          Q(σ.h, c1)})
    }

    produced
  }

  private def getOptimalSnapshotSort(φ: ast.Expression): (Sort, Boolean) = φ match {
    case _ if φ.isPure =>
      (sorts.Snap, true)

    case ast.AccessPredicate(locacc, _) => locacc match {
      case fa: ast.FieldAccess => (toSort(fa.field.typ), false)
      case pa: ast.PredicateAccess => getOptimalSnapshotSort(pa.predicate.body)
      /* TODO: Most likely won't terminate for a predicate that only contains
       *       itself in its body, e.g., predicate P(x) {P(x)}.
       */
    }

    case ast.Implies(e0, φ1) =>
      /* φ1 must be impure, otherwise the first case would have applied. */
      getOptimalSnapshotSort(φ1)

    case ast.And(φ1, φ2) =>
      /* At least one of φ1, φ2 must be impure, otherwise ... */
      getOptimalSnapshotSortFromPair(φ1, φ2, () => (sorts.Snap, false))

    case ast.Ite(_, φ1, φ2) =>
      /* At least one of φ1, φ2 must be impure, otherwise ... */

      def findCommonSort() = {
        val (s1, isPure1) = getOptimalSnapshotSort(φ1)
        val (s2, isPure2) = getOptimalSnapshotSort(φ2)
        val s = if (s1 == s2) s1 else sorts.Snap
        val isPure = isPure1 && isPure2
        (s, isPure)
      }

      getOptimalSnapshotSortFromPair(φ1, φ2, findCommonSort)

    case ast.Forall(_, _, ast.Implies(_, ast.FieldAccessPredicate(ast.FieldAccess(_, f), _))) =>
      /* TODO: See Silicon issue 59. Returning a fresh term here is just a temporary work-around. */
      (toSort(f.typ), false)

    case _ =>
      (sorts.Snap, false)
  }

  private def getOptimalSnapshotSortFromPair(φ1: ast.Expression,
                                             φ2: ast.Expression,
                                             fIfBothPure: () => (Sort, Boolean))
                                            : (Sort, Boolean) = {

    if (φ1.isPure && !φ2.isPure) getOptimalSnapshotSort(φ2)
    else if (!φ1.isPure && φ2.isPure) getOptimalSnapshotSort(φ1)
    else fIfBothPure()
  }

  private def mkSnap(φ: ast.Expression): Term = getOptimalSnapshotSort(φ) match {
    case (sorts.Snap, true) => Unit
    case (sort, _) => fresh(sort)
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
