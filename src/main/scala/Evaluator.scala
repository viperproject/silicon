/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import org.slf4s.Logging
import silver.ast
import silver.ast.utility.Expressions
import silver.verifier.PartialVerificationError
import silver.verifier.errors.PreconditionInAppFalse
import silver.verifier.reasons.{DivisionByZero, ReceiverNull, NegativePermission}
import reporting.Bookkeeper
import interfaces.{Evaluator, Consumer, Producer, VerificationResult, Failure, Success}
import interfaces.state.{Store, Heap, PathConditions, State, StateFactory, StateFormatter, HeapCompressor,
    Chunk, ChunkIdentifier}
import interfaces.decider.Decider
import state.{DefaultContext, PredicateChunkIdentifier, FieldChunkIdentifier, SymbolConvert, DirectChunk,
    DirectFieldChunk}
import state.terms._
import state.terms.implicits._
import state.terms.perms.IsNonNegative
import supporters.{Joiner, Brancher, PredicateSupporter, QuantifiedChunkSupporter}

trait DefaultEvaluator[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
                       S <: State[ST, H, S]]
    extends Evaluator[ST, H, S, DefaultContext]
    { this: Logging with Consumer[DirectChunk, ST, H, S, DefaultContext]
                    with Producer[ST, H, S, DefaultContext]
                    with PredicateSupporter[ST, H, PC, S]
                    with Brancher[ST, H, S, DefaultContext]
                    with Joiner[DefaultContext] =>

  private type C = DefaultContext

  protected val decider: Decider[ST, H, PC, S, C]
  import decider.{fresh, assume}

  protected val stateFactory: StateFactory[ST, H, S]
  import stateFactory._

  protected val symbolConverter: SymbolConvert
  import symbolConverter.toSort

  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val heapCompressor: HeapCompressor[ST, H, S, C]

  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, PC, S]

  def evals(σ: S, es: Seq[ast.Exp], pve: PartialVerificationError, c: C)
           (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

    evals2(σ, es, Nil, pve, c)((ts, c1) =>
      Q(ts, c1))

  private def evals2(σ: S,
                     es: Seq[ast.Exp],
                     ts: List[Term],
                     pve: PartialVerificationError,
                     c: C)
                    (Q: (List[Term], C) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(ts.reverse, c)
    else
      eval(σ, es.head, pve, c)((t, c1) =>
        evals2(σ, es.tail, t :: ts, pve, c1)(Q))
  }

  def eval(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
          | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
          | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        log.debug(s"\nEVAL ${e.pos}: $e")
        log.debug(stateFormatter.format(σ))
        decider.prover.logComment(s"[eval] $e")
    }

    eval2(σ, e, pve, c)((t, c1) => {
      val c2 =
        if (c1.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger => c1.copy(possibleTriggers = c1.possibleTriggers + (pt -> t))
            case _ => c1}
        else
          c1
      Q(t, c2)})
  }

  protected def eval2(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

    /* Since commit 0cf1f26, evaluating unfoldings is a local operation, and it
     * might be tempting to think that we don't need to locally evaluate
     * Implies and Ite anymore. However, that is not true, because not all of
     * them occur in the context of an unfolding. They can also occur in a
     * pre/postcondition such as 'requires b1 ==> b2', in which case Silicon
     * still shouldn't branch.
     */

    /* TODO: LocalEvaluationResults collect contexts as well.
     *       However, only one context can be passed on to Q, and currently
     *       the one from the first LocalEvaluationResult is taken.
     *       This shouldn't be much of a problem, except maybe for debugging,
     *       as long as the context doesn't keep track of any crucial
     *       information. This may not always be the case, however. E.g., the
     *       Wands-Silicon prototype (for the rejected FM'14 paper) uses the
     *       context to record the reserve heap.
     */

    val resultTerm = e match {
      case _: ast.TrueLit => Q(True(), c)
      case _: ast.FalseLit => Q(False(), c)

      case _: ast.NullLit => Q(Null(), c)
      case ast.IntLit(bigval) => Q(IntLiteral(bigval), c)

      case ast.EqCmp(e0, e1) => evalBinOp(σ, e0, e1, Equals, pve, c)(Q)
      case ast.NeCmp(e0, e1) => evalBinOp(σ, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, c)(Q)

      case v: ast.AbstractLocalVar => Q(σ.γ(v), c)

      case _: ast.FullPerm => Q(FullPerm(), c)
      case _: ast.NoPerm => Q(NoPerm(), c)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOp(σ, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, c)((tFP, c1) =>
          failIfDivByZero(σ, tFP, e1, t1, predef.Zero, pve, c1)(Q))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = decider.freshARP()
        assume(tConstraints)
        Q(WildcardPerm(tVar), c)

      case ast.CurrentPerm(locacc) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          decider.getChunk[DirectChunk](σ, σ.h, id, c1) match {
            case Some(ch) => Q(ch.perm, c1)
            case None => Q(NoPerm(), c1)
          })

      case fa: ast.FieldAccess if quantifiedChunkSupporter.isQuantifiedFor(σ.h, fa.field.name) =>
        eval(σ, fa.rcv, pve, c)((tRcvr, c1) => {
          val qvars = c1.quantifiedVariables.filter(qv => tRcvr.existsDefined{case `qv` => true})
          val condition = And(c1.branchConditions)
          quantifiedChunkSupporter.withValue(σ, σ.h, fa.field, qvars, condition, tRcvr, pve, fa, c1)(fvfDef => {
            val fvfDomain = fvfDef.domainDefinition
            assume(fvfDomain +: fvfDef.valueDefinitions)
            val c2 = c1.snapshotRecorder match {
              case Some(sr) =>
                val sr1 = sr.recordSnapshot(fa, c1.branchConditions, fvfDef.lookupReceiver)
                            .recordQPTerms(qvars, c1.branchConditions, fvfDomain +: fvfDef.valueDefinitions)
                val sr2 =
                  if (fvfDef.freshFvf) sr1.recordFvf(fa.field, fvfDef.fvf)
                  else sr1
                c1.copy(snapshotRecorder = Some(sr2))
              case _ => c1}
            Q(fvfDef.lookupReceiver, c2)})})

      case fa: ast.FieldAccess =>
        withChunkIdentifier(σ, fa, true, pve, c)((id, c1) =>
          decider.withChunk[DirectFieldChunk](σ, σ.h, id, None, fa, pve, c1)((ch, c2) => {
            val c3 = c2.snapshotRecorder match {
              case Some(sr) =>
                c2.copy(snapshotRecorder = Some(sr.recordSnapshot(fa, c2.branchConditions, ch.value)))
              case _ => c2}
            Q(ch.value, c3)}))

      case ast.Not(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Not(t0), c1))

      case ast.Minus(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Minus(0, t0), c1))

      case ast.Old(e0) => eval(σ \ σ.g, e0, pve, c)(Q)

      case ast.Let(v, e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ \+ (v.localVar, t0), e1, pve, c1)((t1, c2) =>
            Q(t1, c2)))

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, (t1, t2) => And(t1, t2), pve, c)(Q)

      /* Short-circuiting evaluation of AND */
      case ast.And(e0, e1) =>
        evalDependently(σ, e0, e1, Predef.identity, pve, c)((t0, optT1, c1) => {
          val tAnd = And(t0, optT1.getOrElse(True()))
          Q(tAnd, c1)})

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, (t1, t2) => Or(t1, t2), pve, c)(Q)

      /* Short-circuiting evaluation of OR */
      case ast.Or(e0, e1) =>
        evalDependently(σ, e0, e1, Not, pve, c)((t0, optT1, c1) => {
          val tOr = Or(t0, optT1.getOrElse(True()))
          Q(tOr, c1)})

      case ast.Implies(e0, e1) =>
        evalDependently(σ, e0, e1, Predef.identity, pve, c)((t0, optT1, c1) => {
          val tImplies = Implies(t0, optT1.getOrElse(True()))
          Q(tImplies, c1)})

      case ite @ ast.CondExp(e0, e1, e2) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          branchAndJoin(σ, t0, c1,
            (c2, QB) =>
              eval(σ, e1, pve, c2)(QB),
            (c2, QB) =>
              eval(σ, e2, pve, c2)(QB)
          )((optT1, optT2, cJoined) => {
            val tIte =
              Ite(t0,
                  optT1.getOrElse(fresh("$deadThen", toSort(e1.typ))),
                  optT2.getOrElse(fresh("$deadElse", toSort(e2.typ))))
            Q(tIte, cJoined)
          }))

      /* Integers */

      case ast.Add(e0, e1) =>
        evalBinOp(σ, e0, e1, Plus, pve, c)(Q)

      case ast.Sub(e0, e1) =>
        evalBinOp(σ, e0, e1, Minus, pve, c)(Q)

      case ast.Mul(e0, e1) =>
        evalBinOp(σ, e0, e1, Times, pve, c)(Q)

      case ast.Div(e0, e1) =>
        evalBinOp(σ, e0, e1, Div, pve, c)((tDiv, c1) =>
          failIfDivByZero(σ, tDiv, e1, tDiv.p1, 0, pve, c1)(Q))

      case ast.Mod(e0, e1) =>
        evalBinOp(σ, e0, e1, Mod, pve, c)((tMod, c1) =>
          failIfDivByZero(σ, tMod, e1, tMod.p1, 0, pve, c1)(Q))

      case ast.LeCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.LtCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.GeCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.GtCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Permissions */

      case ast.PermAdd(e0, e1) =>
        evalBinOp(σ, e0, e1, PermPlus, pve, c)(Q)

      case ast.PermSub(e0, e1) =>
        evalBinOp(σ, e0, e1, PermMinus, pve, c)(Q)

      case ast.PermMul(e0, e1) =>
        evalBinOp(σ, e0, e1, PermTimes, pve, c)(Q)

      case ast.IntPermMul(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            Q(IntPermTimes(t0, t1), c2)))

      case ast.PermDiv(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            failIfDivByZero(σ, PermIntDiv(t0, t1), e1, t1, 0, pve, c1)(Q)))

      case ast.PermLeCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.PermLtCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.PermGeCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.PermGtCmp(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evals(σ, eArgs, pve, c)((tArgs, c1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = toSort(dfa.typ)
          val fi = symbolConverter.toFunction(c.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(DomainFApp(fi, tArgs), c1)})

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            val forallWithTriggers = forall.autoTrigger
            (forallWithTriggers, Forall, forallWithTriggers.triggers)
          case exists: ast.Exists =>
            (exists, Exists, Seq())
        }

        val body = eQuant.exp
        val vars = eQuant.variables map (_.localVar)

        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ(vars zip tVars)
        val σQuant = σ \+ γVars

        val c0 = c.copy(quantifiedVariables = tVars ++ c.quantifiedVariables,
                        recordPossibleTriggers = true,
                        possibleTriggers = Map.empty)

        decider.locally[(Quantification, Quantification, C)](QB => {
          val πPre: Set[Term] = decider.π
          eval(σQuant, body, pve, c0)((tBody, c1) => {
            val πDelta = decider.π -- πPre
            evalTriggers(σQuant, eTriggers, pve, c1)((triggers, c2) => {
              val qid = sourceQuant.pos match {
                case pos: ast.HasLineColumn => s"prog.l${pos.line}"
                case _ => s"prog.l${sourceQuant.pos}"}
              val tQuant = Quantification(qantOp, tVars, tBody, triggers, qid)
              val tAuxQuant = Quantification(qantOp, tVars, And(πDelta), triggers, s"$qid-aux")
              val c3 = c2.copy(quantifiedVariables = c2.quantifiedVariables.drop(tVars.length),
                               recordPossibleTriggers = c.recordPossibleTriggers,
                               possibleTriggers = c.possibleTriggers ++ (if (c.recordPossibleTriggers) c2.possibleTriggers else Map()))
              QB(tQuant, tAuxQuant, c3)})})
        }){case (tQuant, tAuxQuant, c1) =>
          assume(tAuxQuant)
          Q(tQuant, c1)
        }

      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val err = PreconditionInAppFalse(fapp)
        val func = c.program.findFunction(funcName)

        evals2(σ, eArgs, Nil, pve, c)((tArgs, c2) => {
          bookkeeper.functionApplications += 1
          val pre = Expressions.instantiateVariables(utils.ast.BigAnd(func.pres), func.formalArgs, eArgs)
          val joinFunctionArgs = tArgs //++ c2a.quantifiedVariables.filterNot(tArgs.contains)
          /* TODO: Does it matter that the above filterNot does not filter out quantified
           *       variables that are not "raw" function arguments, but instead are used
           *       in an expression that is used as a function argument?
           *       E.g., in
           *         forall i: Int :: fun(i*i)
           *       the above filterNot will not remove i from the list of already
           *       used quantified variables because i does not match i*i.
           *       Hence, the joinedFApp will take two arguments, namely, i*i and i,
           *       although the latter is not necessary.
           */
          join(toSort(func.typ), s"joined_${func.name}", joinFunctionArgs, c2)(QB =>
            consume(σ, FullPerm(), pre, err, c2)((_, s, _, c3) => {
              val s1 = s.convert(sorts.Snap)
              val c4 = c3.snapshotRecorder match {
                case Some(sr) =>
                  c3.copy(snapshotRecorder = Some(sr.recordSnapshot(fapp, c3.branchConditions, s1)))
                case _ => c3}
              val tFApp = FApp(symbolConverter.toFunction(func), s1, tArgs)
              val c5 =
                if (c4.recordPossibleTriggers) c4.copy(possibleTriggers = c4.possibleTriggers + (fapp -> tFApp))
                else c4
              QB(tFApp, c5)})
            )((tR, cR) => {
              Q(tR, cR)
            })})

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = c.program.findPredicate(predicateName)

        if (c.cycles(predicate) < config.recursivePredicateUnfoldings()) {
          val c0 = c.incCycleCounter(predicate)

          evals(σ, eArgs, pve, c0)((tArgs, c1) =>
            eval(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsNonNegative(tPerm)) {
              case true =>
                  join(toSort(eIn.typ), "joinedIn", c2.quantifiedVariables, c2)(QB =>
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                    predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                      val c4 = c3.decCycleCounter(predicate)
//                      eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                        QB(tIn, c5))})
                    consume(σ, FullPerm(), acc, pve, c2)((σ1, snap, chs, c3) => {
//                      val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                      val body = pa.predicateBody(c.program).get /* Only non-abstract predicates can be unfolded */
                      produce(σ1 /*\ insγ*/, s => snap.convert(s), tPerm, body, pve, c3)((σ2, c4) => {
                        val c4a = c4.decCycleCounter(predicate)
                        val σ3 = σ2 //\ (g = σ.g)
                        eval(σ3 /*\ σ.γ*/, eIn, pve, c4a)((tIn, c5) => {
                          QB(tIn, c5)})})})
                  )(Q)
              case false =>
                  Failure[ST, H, S](pve dueTo NegativePermission(ePerm))}))
        } else {
          val unknownValue = fresh("recunf", toSort(eIn.typ))
          Q(unknownValue, c)
        }

      /* Sequences */

      case ast.SeqContains(e0, e1) => evalBinOp(σ, e1, e0, SeqIn, pve, c)(Q)
        /* Note the reversed order of the arguments! */

      case ast.SeqAppend(e0, e1) => evalBinOp(σ, e0, e1, SeqAppend, pve, c)(Q)
      case ast.SeqDrop(e0, e1) => evalBinOp(σ, e0, e1, SeqDrop, pve, c)(Q)
      case ast.SeqTake(e0, e1) => evalBinOp(σ, e0, e1, SeqTake, pve, c)(Q)
      case ast.SeqIndex(e0, e1) => evalBinOp(σ, e0, e1, SeqAt, pve, c)(Q)
      case ast.SeqLength(e0) => eval(σ, e0, pve, c)((t0, c1) => Q(SeqLength(t0), c1))
      case ast.EmptySeq(typ) => Q(SeqNil(toSort(typ)), c)
      case ast.RangeSeq(e0, e1) => evalBinOp(σ, e0, e1, SeqRanged, pve, c)(Q)

      case ast.SeqUpdate(e0, e1, e2) =>
        evals2(σ, List(e0, e1, e2), Nil, pve, c)((ts, c1) =>
          Q(SeqUpdate(ts(0), ts(1), ts(2)), c1))

      case ast.ExplicitSeq(es) =>
        evals2(σ, es.reverse, Nil, pve, c)((tEs, c1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(SeqSingleton(te), tSeq))
          assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(tSeq, c1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) => Q(EmptySet(toSort(typ)), c)
      case ast.EmptyMultiset(typ) => Q(EmptyMultiset(toSort(typ)), c)

      case ast.ExplicitSet(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(tSet, c1)})

      case ast.ExplicitMultiset(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(tMultiset, c1)})

      case ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(σ, e0, e1, SetUnion, pve, c)(Q)
        case _: ast.MultisetType => evalBinOp(σ, e0, e1, MultisetUnion, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(σ, e0, e1, SetIntersection, pve, c)(Q)
        case _: ast.MultisetType => evalBinOp(σ, e0, e1, MultisetIntersection, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.SetType => evalBinOp(σ, e0, e1, SetSubset, pve, c)(Q)
        case _: ast.MultisetType => evalBinOp(σ, e0, e1, MultisetSubset, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(σ, e0, e1, SetDifference, pve, c)(Q)
        case _: ast.MultisetType => evalBinOp(σ, e0, e1, MultisetDifference, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.SetType => evalBinOp(σ, e0, e1, SetIn, pve, c)(Q)
        case _: ast.MultisetType => evalBinOp(σ, e0, e1, (t0, t1) => MultisetCount(t1, t0), pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.SetType => eval(σ, e0, pve, c)((t0, c1) => Q(SetCardinality(t0), c1))
        case _: ast.MultisetType => eval(σ, e0, pve, c)((t0, c1) => Q(MultisetCardinality(t0), c1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }

      /* Unexpected nodes */

      case _: ast.InhaleExhaleExp =>
        Failure[ST, H, S](utils.consistency.createUnexpectedInhaleExhaleExpressionError(e))
    }

    resultTerm
  }

  def withChunkIdentifier(σ: S,
                          locacc: ast.LocationAccess,
                          assertRcvrNonNull: Boolean,
                          pve: PartialVerificationError,
                          c: C)
                         (Q: (ChunkIdentifier, C) => VerificationResult)
                         : VerificationResult =

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          if (assertRcvrNonNull)
            decider.assert(σ, tRcvr !== Null()){
              case true => Q(FieldChunkIdentifier(tRcvr, field.name), c1)
              case false => Failure[ST, H, S](pve dueTo ReceiverNull(locacc))}
          else
            Q(FieldChunkIdentifier(tRcvr, field.name), c1))

      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(σ, eArgs, pve, c)((tArgs, c1) =>
          Q(PredicateChunkIdentifier(predicateName, tArgs), c1))
    }

  private def evalBinOp[T <: Term]
                       (σ: S,
                        e0: ast.Exp,
                        e1: ast.Exp,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
                        c: C)
                       (Q: (T, C) => VerificationResult)
                       : VerificationResult = {

    eval(σ, e0, pve, c)((t0, c1) =>
      eval(σ, e1, pve, c1)((t1, c2) =>
        Q(termOp(t0, t1), c2)))
  }

  private def failIfDivByZero(σ: S,
                              t: Term,
                              eDivisor: ast.Exp,
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              c: C)
                             (Q: (Term, C) => VerificationResult)
                             : VerificationResult = {

    decider.assert(σ, tDivisor !== tZero){
      case true => Q(t, c)
      case false => Failure[ST, H, S](pve dueTo DivisionByZero(eDivisor))
    }
  }

  /* TODO: The CP-style in which Silicon's main components are written makes it hard to work
   *       with sequences. evalTriggers, evals and execs all share the same pattern, they
   *       essentially recurse over a sequence and accumulate results, where results can be
   *       terms, verification results, contexts, or any combination of these.
   *       It would be nice to find a (probably crazy functional) abstraction that avoids
   *       having to implement that pattern over and over again.
   *
   */
  private def evalTriggers(σ: S, silTriggers: Seq[ast.Trigger], pve: PartialVerificationError, c: C)
                          (Q: (List[Trigger], C) => VerificationResult)
                          : VerificationResult =

    evalTriggers(σ, silTriggers, Nil, pve, c)(Q)

  private def evalTriggers(σ: S,
                           silTriggers: Seq[ast.Trigger],
                           triggers: List[Trigger],
                           pve: PartialVerificationError,
                           c: C)
                          (Q: (List[Trigger], C) => VerificationResult)
                          : VerificationResult = {

    if (silTriggers.isEmpty)
      Q(triggers.reverse, c)
    else
      evalTrigger(σ, silTriggers.head, pve, c)((t, c1) =>
        evalTriggers(σ, silTriggers.tail, t :: triggers, pve, c1)(Q))
  }

  private def evalTrigger(σ: S, trigger: ast.Trigger, pve: PartialVerificationError, c: C)
                         (Q: (Trigger, C) => VerificationResult)
                         : VerificationResult = {

    val (cachedTriggerTerms, remainingTriggerExpressions) =
      trigger.exps.map {
        case ast.Old(e) => e /* Warning! For heap-dep. function applications, old(e) probably matters */
        case e => e
      }.map {
        case fapp: ast.FuncApp =>
          /** Heap-dependent functions that are used as triggers should be used
            * in the limited version, because it allows for more instantiations.
            * Keep this code in sync with [[supporters.ExpressionTranslator.translate]]
            *
            */
          val cachedTrigger = c.possibleTriggers.get(fapp).collect{case fa: FApp => fa.limitedVersion}

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(fapp))

        case pt: ast.PossibleTrigger =>
          val cachedTrigger = c.possibleTriggers.get(pt)

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(pt))

        case e => (None, Some(e))
      }.unzip match {
        case (optCachedTriggerTerms, optRemainingTriggerExpressions) =>
          (optCachedTriggerTerms.flatten, optRemainingTriggerExpressions.flatten)
      }

    /* Reasons for why a trigger wasn't recorded while evaluating the body include:
     *   - It did not occur in the body
     *   - The evaluation of the body terminated early, for example, because the
     *     LHS of an implication evaluated to false
     */

    var optRemainingTriggerTerms: Option[Seq[Term]] = None
    val πPre: Set[Term] = decider.π
    var πAux: Set[Term] = Set()

    /* TODO: Evaluate as many remaining expressions as possible, i.e. don't
     *       stop if evaluating one fails
     */
    val r =
      evals(σ, remainingTriggerExpressions, pve, c)((remainingTriggerTerms, c1) => {
        optRemainingTriggerTerms = Some(remainingTriggerTerms)
        πAux = decider.π -- πPre
        Success()})

    /* TODO: Here is an example where evaluating remainingTriggerExpressions will
     *       fail: Assume a conjunction f(x) && g(x) where f(x) is the
     *       precondition of g(x). This gives rise to the trigger {f(x), g(x)}.
     *       If the two trigger expressions are evaluated individually, evaluating
     *       the second will fail because its precondition doesn't hold.
     *       For example, let f(x) be "x in xs" (and assume that this, via other
     *       path conditions, implies that x != null), and let g(x) be "y.f in xs".
     *       Evaluating the latter will currently fail when evaluating y.f because
     *       y on its own (i.e., without having assumed y in xs) might be null.
     *
     *       What might be possible is to merely translate (instead of evaluate)
     *       triggers, where the difference is that translating does not entail
     *       any checks such as checking for non-nullity.
     *       In case of applications of heap. dep. functions this won't be
     *       straight-forward, because the resulting FApp-term expects a snapshot,
     *       which is computed by (temporarily) consuming the function's
     *       precondition.
     *       We could replace each concrete snapshot occurring in an FApp-term by
     *       a quantified snapshot, but that might make the chosen triggers invalid
     *       because some trigger sets might no longer cover all quantified
     *       variables.
     */

    (r, optRemainingTriggerTerms) match {
      case (Success(), Some(remainingTriggerTerms)) =>
        assume(πAux)
        Q(Trigger(cachedTriggerTerms ++ remainingTriggerTerms), c)
      case _ =>
        bookkeeper.logfiles("evalTrigger").println(s"Couldn't translate some of these triggers:\n  $remainingTriggerExpressions\nReason:\n  $r")
        Q(Trigger(cachedTriggerTerms), c)
    }
  }

  /* Evaluates `e0` to `t0`, assumes `t0Transformer(t0)`, and afterwards only
   * evaluates `e1` if the current state is consistent. That is, `e1` is only
   * evaluated if `t0Transformer(t0)` does not contradict the current path
   * conditions. This method can be used to evaluate short-circuiting operators
   * such as conjunction, disjunction or implication.
   *
   * Attention: `e1` is not expected to branch; if it does, an exception will be
   * thrown.
   */
  private def evalDependently(σ: S,
                              e0: ast.Exp,
                              e1: ast.Exp,
                              t0Transformer: Term => Term,
                              pve: PartialVerificationError, c: C)
                             (Q: (Term, Option[Term], C) => VerificationResult)
                             : VerificationResult = {

      var πPre: Set[Term] = Set()
      var optT1: Option[Term] = None /* e1 won't be evaluated if e0 cannot be satisfied */
      var πAux: Set[Term] = Set()
      var optInnerC: Option[C] = None

      eval(σ, e0, pve, c)((t0, c1) => {
        πPre = decider.π

        decider.pushScope()

        val guard = t0Transformer(t0)
        var originalChunks: Option[Iterable[Chunk]] = None
        val r =
          branch(σ, guard, c1,
            (c2: C) => {
              if (c2.retrying) {
                originalChunks = Some(σ.h.values)
                heapCompressor.compress(σ, σ.h, c2)
              }
              eval(σ, e1, pve, c2)((t1, c3) => {
                assert(optT1.isEmpty, s"Unexpected branching occurred while locally evaluating $e1")
                optT1 = Some(t1)
                πAux = decider.π -- (πPre + guard)
                  /* Removing guard from πAux is crucial, it is not part of the aux. terms */
                optInnerC = Some(c3)
                Success()})},
            (c2: C) =>
              Success())

        /* See comment in DefaultDecider.tryOrFail */
        originalChunks match {
          case Some(chunks) => σ.h.replace(chunks)
          case None => /* Nothing to do here */
        }

        decider.popScope()

        r && {
          assume(Implies(guard, And(πAux)))
          val c2 = optInnerC.map(_.copy(branchConditions = c1.branchConditions)).getOrElse(c1)
          Q(t0, optT1, c2)}})
  }
}
