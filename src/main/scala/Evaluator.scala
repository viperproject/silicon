/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon

import com.weiglewilczek.slf4s.Logging
import silver.ast.utility.Expressions
import silver.verifier.PartialVerificationError
import silver.verifier.errors.PreconditionInAppFalse
import silver.verifier.reasons.{DivisionByZero, ReceiverNull, NegativePermission}
import reporting.Bookkeeper
import interfaces.{Evaluator, Consumer, Producer, VerificationResult, Failure, Success}
import interfaces.state.{ChunkIdentifier, Store, Heap, PathConditions, State, StateFormatter, StateFactory, FieldChunk}
import interfaces.decider.Decider
import state.{DefaultContext, PredicateChunkIdentifier, FieldChunkIdentifier, SymbolConvert, DirectChunk,
    DirectFieldChunk}
import state.terms._
import state.terms.predef.`?s`
import state.terms.implicits._
import state.terms.perms.IsPositive

trait DefaultEvaluator[ST <: Store[ST],
                       H <: Heap[H],
                       PC <: PathConditions[PC],
											 S <: State[ST, H, S]]
		extends Evaluator[ST, H, S, DefaultContext] with HasLocalState
		{ this: Logging with Consumer[DirectChunk, ST, H, S, DefaultContext]
										with Producer[ST, H, S, DefaultContext]
										with Brancher[ST, H, S, DefaultContext]
										with Joiner[ST, H, S, DefaultContext] =>

  private type C = DefaultContext

	protected val decider: Decider[ST, H, PC, S, C]
	import decider.{fresh, assume}

	protected val stateFactory: StateFactory[ST, H, S]
	import stateFactory._

	protected val symbolConverter: SymbolConvert
	import symbolConverter.toSort

  protected val stateUtils: StateUtils[ST, H, PC, S, C]
	protected val stateFormatter: StateFormatter[ST, H, S, String]
	protected val config: Config
	protected val bookkeeper: Bookkeeper

	/*private*/ var fappCache: Map[Term, Set[Term]] = Map()
	/*private*/ var fappCacheFrames: Stack[Map[Term, Set[Term]]] = Stack()

	def evals(σ: S, es: Seq[ast.Expression], pve: PartialVerificationError, c: C)
			     (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

		evals2(σ, es, Nil, pve, c)((ts, c1) =>
			Q(ts, c1))

	private def evals2(σ: S,
                     es: Seq[ast.Expression],
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

	def eval(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {

		eval2(σ, e, pve, c)((t, c1) => {
      val c2 =
        if (c1.recordPossibleTriggers)
          e match {
            case pt: silver.ast.PossibleTrigger => c1.copy(possibleTriggers = c1.possibleTriggers + (pt -> t))
            case _ => c1}
        else
          c1
			Q(t, c2)})
  }

  protected def eval2(σ: S, e: ast.Expression, pve: PartialVerificationError, c: C)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

		/* For debugging only */
		e match {
			case  _: ast.True | _: ast.False | _: ast.NullLiteral | _: ast.IntegerLiteral | _: ast.FullPerm | _: ast.NoPerm
          | _: ast.Variable | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.ResultLiteral
          | _: ast.WildcardPerm | _: ast.FieldAccess =>

			case _ =>
        logger.debug(s"\nEVAL ${e.pos}: $e")
				logger.debug(stateFormatter.format(σ))
        decider.prover.logComment(s"[eval] $e")
		}

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
      case ast.True() => Q(True(), c)
      case ast.False() => Q(False(), c)

      case ast.NullLiteral() => Q(Null(), c)
      case ast.IntegerLiteral(bigval) => Q(IntLiteral(bigval), c)

      case ast.Equals(e0, e1) => evalBinOp(σ, e0, e1, Equals, pve, c)(Q)
      case ast.Unequals(e0, e1) => evalBinOp(σ, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, c)(Q)

      case v: ast.Variable => Q(σ.γ(v), c)

      case _: ast.FullPerm => Q(FullPerm(), c)
      case _: ast.NoPerm => Q(NoPerm(), c)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOp(σ, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, c)((tFP, c1) =>
          failIfDivByZero(σ, tFP, e1, t1, predef.Zero, pve, c1)(Q))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = stateUtils.freshARP()
        assume(tConstraints)
        Q(WildcardPerm(tVar), c)

      case ast.CurrentPerm(locacc) =>
        withChunkIdentifier(σ, locacc, true, pve, c)((id, c1) =>
          decider.getChunk[DirectChunk](σ, σ.h, id, c1) match {
            case Some(ch) => Q(ch.perm, c1)
            case None => Q(NoPerm(), c1)
          })

      case fa: ast.FieldAccess =>
        withChunkIdentifier(σ, fa, true, pve, c)((id, c1) =>
          decider.withChunk[DirectFieldChunk](σ, σ.h, id, None, fa, pve, c1)(ch => {
            val c2 = c1.snapshotRecorder match {
              case Some(sr) =>
                c1.copy(snapshotRecorder = Some(sr.copy(locToChunk = sr.locToChunk + (fa -> ch.id))))
              case _ => c1}
            Q(ch.value, c2)}))

      case ast.Not(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Not(t0), c1))

      case ast.IntNeg(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Minus(0, t0), c1))

      case ast.Old(e0) => eval(σ \ σ.g, e0, pve, c)(Q)

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
        evalBinOp(σ, e0, e1, Or, pve, c)(Q)

      /* Short-circuiting evaluation of OR */
      case ast.Or(e0, e1) =>
        evalDependently(σ, e0, e1, Not, pve, c)((t0, optT1, c1) => {
          val tOr = Or(t0, optT1.getOrElse(True()))
          Q(tOr, c1)})

      case ast.Implies(e0, e1) =>
        evalDependently(σ, e0, e1, Predef.identity, pve, c)((t0, optT1, c1) => {
          val tImplies = Implies(t0, optT1.getOrElse(True()))
          Q(tImplies, c1)})

      case ite @ ast.Ite(e0, e1, e2) =>
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

      case ast.IntPlus(e0, e1) =>
        evalBinOp(σ, e0, e1, Plus, pve, c)(Q)

      case ast.IntMinus(e0, e1) =>
        evalBinOp(σ, e0, e1, Minus, pve, c)(Q)

      case ast.IntTimes(e0, e1) =>
        evalBinOp(σ, e0, e1, Times, pve, c)(Q)

      case ast.IntDiv(e0, e1) =>
        evalBinOp(σ, e0, e1, Div, pve, c)((tDiv, c1) =>
          failIfDivByZero(σ, tDiv, e1, tDiv.p1, 0, pve, c1)(Q))

      case ast.IntMod(e0, e1) =>
        evalBinOp(σ, e0, e1, Mod, pve, c)((tMod, c1) =>
          failIfDivByZero(σ, tMod, e1, tMod.p1, 0, pve, c1)(Q))

      case ast.IntLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.IntLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.IntGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.IntGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Permissions */

      case ast.PermPlus(e0, e1) =>
        evalBinOp(σ, e0, e1, PermPlus, pve, c)(Q)

      case ast.PermMinus(e0, e1) =>
        evalBinOp(σ, e0, e1, PermMinus, pve, c)(Q)

      case ast.PermTimes(e0, e1) =>
        evalBinOp(σ, e0, e1, PermTimes, pve, c)(Q)

      case ast.IntPermTimes(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            Q(IntPermTimes(t0, t1), c2)))

      case ast.PermIntDiv(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            failIfDivByZero(σ, PermIntDiv(t0, t1), e1, t1, 0, pve, c1)(Q)))

      case ast.PermLE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtMost, pve, c)(Q)

      case ast.PermLT(e0, e1) =>
        evalBinOp(σ, e0, e1, Less, pve, c)(Q)

      case ast.PermGE(e0, e1) =>
        evalBinOp(σ, e0, e1, AtLeast, pve, c)(Q)

      case ast.PermGT(e0, e1) =>
        evalBinOp(σ, e0, e1, Greater, pve, c)(Q)

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evals(σ, eArgs, pve, c)((tArgs, c1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = toSort(dfa.typ)
          val fi = symbolConverter.toFunction(c.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(DomainFApp(fi, tArgs), c1)})

      case quant: ast.Quantified /*if config.disableLocalEvaluations()*/ =>
        val (triggerQuant, tQuantOp, silTriggers) = quant match {
          case fa: ast.Forall => (fa.autoTrigger, Forall, fa.autoTrigger.triggers)
          case ex: ast.Exists => (ex, Exists, Seq())
        }

        val body = triggerQuant.exp
        val vars = triggerQuant.variables map (_.localVar)

        val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
        val γVars = Γ(vars zip tVars)
        val σQuant = σ \+ γVars

        val c0 = c.copy(quantifiedVariables = tVars ++ c.quantifiedVariables,
                        recordPossibleTriggers = true,
                        possibleTriggers = Map.empty,
                        additionalTriggers = Nil)

        decider.locally[(Set[Term], Term, C)](QB => {
          val πPre: Set[Term] = decider.π
          eval(σQuant, body, pve, c0)((tBody, c1) => {
            val πDelta = decider.π -- πPre
            evalTriggers(σQuant, silTriggers, pve, c1)((triggers, c2) => {
              val actualTriggers = triggers ++ c2.additionalTriggers.map(t => Trigger(t))
              val πAux = state.utils.extractAuxiliaryTerms(πDelta, tQuantOp, tVars)
              val tQuant = Quantification(tQuantOp, tVars, tBody, actualTriggers)
              val c3 = c2.copy(quantifiedVariables = c2.quantifiedVariables.drop(tVars.length),
                               recordPossibleTriggers = c.recordPossibleTriggers,
                               possibleTriggers = c.possibleTriggers ++ (if (c.recordPossibleTriggers) c2.possibleTriggers else Map()),
                               additionalTriggers = c.additionalTriggers ++ (if (c.recordPossibleTriggers) c2.additionalTriggers else Nil))
              QB(πAux, tQuant, c3)})})
        }){case (πAux, tQuant, c1) =>
          assume(πAux)
          Q(tQuant, c1)
        }

      /* Only evaluate the function application; relies on functions being axiomatised */
      case fapp @ ast.FuncApp(funcName, eArgs) if !config.disableFunctionAxiomatization() =>
        val err = PreconditionInAppFalse(fapp)
        val func = c.program.findFunction(funcName)

        evals2(σ, eArgs, Nil, pve, c)((tArgs, c2) => {
          bookkeeper.functionApplications += 1
          val pre = Expressions.instantiateVariables(ast.utils.BigAnd(func.pres), func.formalArgs, eArgs)
          val c2a = c2.snapshotRecorder match {
            case Some(sr) => c2.copy(snapshotRecorder = Some(sr.copy(currentSnap = `?s`)))
            case _ => c2
          }
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
          join(toSort(func.typ), s"joined_${func.name}", joinFunctionArgs, c2a)(QB =>
            consume(σ, FullPerm(), pre, err, c2a)((_, s, _, c3) => {
              val c4 = c3.snapshotRecorder match {
                case Some(sr) =>
                  val sr1 = sr.copy(currentSnap = c2.snapshotRecorder.get.currentSnap,
                                   fappToSnap = sr.fappToSnap + (fapp -> sr.currentSnap))
                  c3.copy(snapshotRecorder = Some(sr1))
                case _ => c3}
              val tFApp = FApp(symbolConverter.toFunction(func), s.convert(sorts.Snap), tArgs)
              val c5 = c4.copy(possibleTriggers = c4.possibleTriggers + (fapp -> tFApp))
              QB(tFApp, c5)})
            )((tR, cR) => {
              Q(tR, cR)
            })})

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = c.program.findPredicate(predicateName)

        if (c.cycles(predicate) < config.recursivePredicateUnfoldings()) {
          val c0a = c.incCycleCounter(predicate)
          eval(σ, ePerm, pve, c0a)((tPerm, c1) => {
            decider.assert(σ, IsPositive(tPerm)){
              case true =>
                evals(σ, eArgs, pve, c1)((tArgs, c2) =>
                  join(toSort(eIn.typ), "joinedIn", c2.quantifiedVariables, c2)(QB => {
                    consume(σ, FullPerm(), acc, pve, c2)((σ1, snap, chs, c3) => {
                      val c3a = c3.snapshotRecorder match {
                        case Some(sr) =>
                          c3.copy(snapshotRecorder = Some(sr.copy(currentSnap = sr.chunkToSnap(chs(0).id))))
                        case _ => c3}
                      val body = pa.predicateBody(c.program)
                      produce(σ1, s => snap.convert(s), tPerm, body, pve, c3a)((σ2, c4) => {
                        val c4a = c4.decCycleCounter(predicate)
                        val σ3 = σ2 \ (g = σ.g)
                        eval(σ3, eIn, pve, c4a)((tIn, c5) => {
                          QB(tIn, c5)})})})
                  })(Q))
              case false =>
                Failure[ST, H, S](pve dueTo NegativePermission(ePerm))}})
        } else {
          val unknownValue = fresh("recunf", toSort(eIn.typ))
          Q(unknownValue, c)
        }

      /* Sequences */

      case ast.SeqIn(e0, e1) => evalBinOp(σ, e1, e0, SeqIn, pve, c)(Q)
        /* Note the reversed order of the arguments! */

      case silver.ast.SeqAppend(e0, e1) => evalBinOp(σ, e0, e1, SeqAppend, pve, c)(Q)
      case silver.ast.SeqDrop(e0, e1) => evalBinOp(σ, e0, e1, SeqDrop, pve, c)(Q)
      case silver.ast.SeqTake(e0, e1) => evalBinOp(σ, e0, e1, SeqTake, pve, c)(Q)
      case ast.SeqAt(e0, e1) => evalBinOp(σ, e0, e1, SeqAt, pve, c)(Q)
      case silver.ast.SeqLength(e0) => eval(σ, e0, pve, c)((t0, c1) => Q(SeqLength(t0), c1))
      case silver.ast.EmptySeq(typ) => Q(SeqNil(toSort(typ)), c)
      case ast.SeqRanged(e0, e1) => evalBinOp(σ, e0, e1, SeqRanged, pve, c)(Q)

      case silver.ast.SeqUpdate(e0, e1, e2) =>
        evals2(σ, List(e0, e1, e2), Nil, pve, c)((ts, c1) =>
          Q(SeqUpdate(ts(0), ts(1), ts(2)), c1))

      case silver.ast.ExplicitSeq(es) =>
        evals2(σ, es.reverse, Nil, pve, c)((tEs, c1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(SeqSingleton(te), tSeq))
          assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(tSeq, c1)})

      /* Sets and multisets */

      case silver.ast.EmptySet(typ) => Q(EmptySet(toSort(typ)), c)
      case silver.ast.EmptyMultiset(typ) => Q(EmptyMultiset(toSort(typ)), c)

      case silver.ast.ExplicitSet(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(tSet, c1)})

      case silver.ast.ExplicitMultiset(es) =>
        evals2(σ, es, Nil, pve, c)((tEs, c1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(tMultiset, c1)})

      case silver.ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetUnion, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetUnion, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIntersection, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIntersection, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetSubset, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetSubset, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetDifference, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetDifference, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.types.Set => evalBinOp(σ, e0, e1, SetIn, pve, c)(Q)
        case _: ast.types.Multiset => evalBinOp(σ, e0, e1, MultisetIn, pve, c)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case silver.ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.types.Set => eval(σ, e0, pve, c)((t0, c1) => Q(SetCardinality(t0), c1))
        case _: ast.types.Multiset => eval(σ, e0, pve, c)((t0, c1) => Q(MultisetCardinality(t0), c1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }

      case _: ast.InhaleExhale =>
        Failure[ST, H, S](ast.Consistency.createUnexpectedInhaleExhaleExpressionError(e))
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
			                  e0: ast.Expression,
                        e1: ast.Expression,
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
                              eDivisor: ast.Expression,
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

    val (optCachedTriggerTerms, optRemainingTriggerExpressions) =
      trigger.exps.map {
        case ast.Old(e) => e
        case e => e
      }.map {
        case fapp: ast.FuncApp =>
          val cachedTrigger = c.possibleTriggers.get(fapp).collect{case fa: FApp => fa.limitedVersion}

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(fapp))

        case pt: silver.ast.PossibleTrigger =>
          val cachedTrigger = c.possibleTriggers.get(pt)

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(pt))

        case e => (None, Some(e))
      }.unzip

    if (optRemainingTriggerExpressions.flatten.nonEmpty)
      /* Reasons for why a trigger wasn't recorded while evaluating the body include:
       *   - It did not occur in the body
       *   - The evaluation of the body terminated early, for example, because the
       *     LHS of an implication evaluated to false
       */
      logger.debug(s"Didn't translate some triggers: ${optRemainingTriggerExpressions.flatten}")

    /* TODO: Translate remaining triggers - which is currently not directly possible.
     *       For example, assume a conjunction f(x) && g(x) where f(x) is the
     *       precondition of g(x). This gives rise to the trigger {f(x), g(x)}.
     *       If the two trigger expressions are evaluated individually, evaluating
     *       the second will fail because its precondition doesn't hold.
     *       For example, let f(x) be "x in xs" (and assume that this, via other
     *       path conditions, implies that x != null), and let g(x) be "y.f in xs".
     *       Evaluating the latter will currently fail when evaluating y.f because
     *       y on its own (i.e., without having assumed y in xs) might be null.
     *
     *       What should probably be done is to merely translate (instead of
     *       evaluate) triggers, where the difference is that translating does not
     *       entail any checks such as checking for non-nullity.
     *       In case of applications of heap. dep. functions this won't be
     *       straight-forward, because the resulting FApp-term expects a snapshot,
     *       which is computed by (temporarily) consuming the function's
     *       precondition.
     *       We could replace each concrete snapshot occurring in an FApp-term by
     *       a quantified snapshot, but that might make the chosen triggers invalid
     *       because some trigger sets might no longer cover all quantified
     *       variables.
     */
//    evals(σ, optRemainingTriggerExpressions.flatten, pve, c)((ts, c1) =>
//      Q(Trigger(ts ++ fappTriggers.flatten), c1))
    Q(Trigger(optCachedTriggerTerms.flatten), c)
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
                              e0: ast.Expression,
                              e1: ast.Expression,
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
        val r =
          branch(σ, guard, c1,
            (c2: C) =>
              eval(σ, e1, pve, c2)((t1, c3) => {
                assert(optT1.isEmpty, s"Unexpected branching occurred while locally evaluating $e1")
                optT1 = Some(t1)
                πAux = decider.π -- (πPre + guard)
                  /* Removing guard from πAux is crucial, it is not part of the aux. terms */
                optInnerC = Some(c3)
                Success()}),
            (c2: C) =>
              Success())

        decider.popScope()

        r && {
          val tAux = πAux
          assume(tAux)
          Q(t0, optT1, optInnerC.getOrElse(c1))}})
  }

	override def pushLocalState() {
		fappCacheFrames = fappCache +: fappCacheFrames
		super.pushLocalState()
	}

	override def popLocalState() {
		fappCache = fappCacheFrames.head
		fappCacheFrames = fappCacheFrames.tail
		super.popLocalState()
	}
}
