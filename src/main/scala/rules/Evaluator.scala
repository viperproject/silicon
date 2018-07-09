/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.rules

import viper.silver.ast
import viper.silver.ast.Info
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.PreconditionInAppFalse
import viper.silver.verifier.reasons._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.implicits._
import viper.silicon.state.terms.perms.{BigPermSum, IsNonNegative, IsPositive}
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silicon.{EvaluateRecord, Map, SymbExLogger, TriggerSets}

/* TODO: With the current design w.r.t. parallelism, eval should never "move" an execution
 *       to a different verifier. Hence, consider not passing the verifier to continuations
 *       of eval.
 */

trait EvaluationRules extends SymbolicExecutionRules {
  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult

  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp],
                     es2: Seq[ast.Exp],
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Verifier) => VerificationResult)
                    : VerificationResult
}

object evaluator extends EvaluationRules with Immutable {
  import consumer._
  import producer._

  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult =

    evals2(s, es, Nil, pvef, v)(Q)

  private def evals2(s: State, es: Seq[ast.Exp], ts: List[Term], pvef: ast.Exp => PartialVerificationError, v: Verifier)
                    (Q: (State, List[Term], Verifier) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(s, ts.reverse, v)
    else
      eval(s, es.head, pvef(es.head), v)((s1, t, v1) =>
        evals2(s1, es.tail, t :: ts, pvef, v1)(Q))
  }

  /** Wrapper Method for eval, for logging. See Executor.scala for explanation of analogue. **/
  @inline
  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult = {

    val sepIdentifier = SymbExLogger.currentLog().insert(new EvaluateRecord(e, s, v.decider.pcs))
    eval3(s, e, pve, v)((s1, t, v1) => {
      SymbExLogger.currentLog().collapse(e, sepIdentifier)
      Q(s1, t, v1)})
  }

  def eval3(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
           (Q: (State, Term, Verifier) => VerificationResult)
           : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
            | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
            | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        v.logger.debug(s"\nEVAL ${viper.silicon.utils.ast.sourceLineColumn(e)}: $e")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.partiallyConsumedHeap.nonEmpty)
          v.logger.debug("pcH = " + s.partiallyConsumedHeap.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        s.oldHeaps.get(Verifier.MAGIC_WAND_LHS_STATE_LABEL) match {
          case Some(hLhs) =>   v.logger.debug("hLhs = " + v.stateFormatter.format(hLhs))
          case None =>
        }
        v.decider.prover.comment(s"[eval] $e")
    }

    /* Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * Also deactivate magic wand's recording of consumed and produced permissions: if the
     * evaluation to perform involves consuming or producing permissions, e.g. because of
     * an unfolding expression, these should not be recorded.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    eval2(s1, e, pve, v)((s2, t, v1) => {
      val s3 =
        if (s2.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (pt -> t))
            case fa: ast.FieldAccess if s2.qpFields.contains(fa.field) =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (fa -> t))
            case _ =>
              s2}
        else
          s2
      val s4 = s3.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s4, t, v1)})
  }

  protected def eval2(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult)
                     : VerificationResult = {

    val resultTerm = e match {
      case _: ast.TrueLit => Q(s, True(), v)
      case _: ast.FalseLit => Q(s, False(), v)

      case _: ast.NullLit => Q(s, Null(), v)
      case ast.IntLit(bigval) => Q(s, IntLiteral(bigval), v)

      case ast.EqCmp(e0, e1) => evalBinOp(s, e0, e1, Equals, pve, v)(Q)
      case ast.NeCmp(e0, e1) => evalBinOp(s, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, v)(Q)

      case x: ast.AbstractLocalVar => Q(s, s.g(x), v)

      case _: ast.FullPerm => Q(s, FullPerm(), v)
      case _: ast.NoPerm => Q(s, NoPerm(), v)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOp(s, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, v)((s1, tFP, v1) =>
          failIfDivByZero(s1, tFP, e1, t1, predef.Zero, pve, v1)(Q))

      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = v.decider.freshARP()
        v.decider.assume(tConstraints)
        /* TODO: Only record wildcards in State.constrainableARPs that are used in exhale
         *       position. Currently, wildcards used in inhale position (only) may not be removed
         *       from State.constrainableARPs (potentially inefficient, but should be sound).
         *
         *       Probably better in general: change evaluator signature such that, in addition to
         *       the resulting term, further data about the evaluation process (e.g. a mapping
         *       from expressions to terms, fresh wildcards, ...) is returned.
         *
         *       Alternative (for just wildcards): introduce WildcardPerm, extract them from the
         *       term returned by eval, mark as constrainable on client-side (e.g. in consumer).
         */
        val s1 =
          s.copy(functionRecorder = s.functionRecorder.recordArp(tVar, tConstraints))
           .setConstrainable(Seq(tVar), true)
        Q(s1, tVar, v)

      case fa: ast.FieldAccess if s.qpFields.contains(fa.field) =>
        eval(s, fa.rcv, pve, v)((s1, tRcvr, v1) => {
          val (relevantChunks, _) =
            quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s1.h, BasicChunkIdentifier(fa.field.name))
          s1.smCache.get((fa.field, relevantChunks)) match {
            case Some((fvfDef: SnapshotMapDefinition, totalPermissions)) if !Verifier.config.disableValueMapCaching() =>
              /* The next assertion must be made if the FVF definition is taken from the cache;
               * in the other case it is part of quantifiedChunkSupporter.withValue.
               */
              v1.decider.assert(IsPositive(totalPermissions.replace(`?r`, tRcvr))) {
                case false =>
                  Failure(pve dueTo InsufficientPermission(fa))
                case true =>
                  v1.decider.assume(fvfDef.valueDefinitions)
                    /* Re-emit definition since the previous definition could be nested under
                     * an auxiliary quantifier (resulting from the evaluation of some Silver
                     * quantifier in whose body field 'fa.field' was accessed)
                     * which is protected by a trigger term that we currently don't have.
                     */
                  val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                  val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup)
                  val s2 = s1.copy(functionRecorder = fr1)
                  Q(s2, fvfLookup, v1)}
            case _ =>
              val totalPermissions = BigPermSum(relevantChunks.map(_.perm), Predef.identity)
              v1.decider.assert(IsPositive(totalPermissions.replace(`?r`, tRcvr))) {
                case false =>
                  Failure(pve dueTo InsufficientPermission(fa))
                case true =>
                  val (fvf, fvfValueDefs, None) =
                    quantifiedChunkSupporter.summarise(s1, relevantChunks, Seq(`?r`), fa.field, None, v1)
                  v1.decider.assume(fvfValueDefs)
                  val smLookup = Lookup(fa.field.name, fvf, tRcvr)
                  val smDef = SnapshotMapDefinition(fa.field, fvf, fvfValueDefs, Seq())
                  val fr2 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, smLookup)
                                               .recordFvfAndDomain(smDef)
                  val smCache2 =
                    if (Verifier.config.disableValueMapCaching()) s1.smCache
                    else s1.smCache + ((fa.field, relevantChunks) -> (smDef, totalPermissions))
                  val s2 = s1.copy(functionRecorder = fr2,
                                   smCache = smCache2)
                  Q(s2, smLookup, v1)}}})

      case fa: ast.FieldAccess =>
        evalLocationAccess(s, fa, pve, v)((s1, name, tArgs, v1) => {
          val id = BasicChunkIdentifier(name)
          val ve = pve dueTo InsufficientPermission(fa)
          chunkSupporter.lookup(s1, s1.h, id, tArgs, ve, v1)((s2, h2, tSnap, v2) => {
            val fr = s2.functionRecorder.recordSnapshot(fa, v2.decider.pcs.branchConditions, tSnap)
            val s3 = s2.copy(h = h2, functionRecorder = fr)
            Q(s3, tSnap, v1)
          })
        })

      case ast.Not(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, Not(t0), v1))

      case ast.Minus(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, Minus(0, t0), v1))

      case ast.Old(e0) =>
        evalInOldState(s, Verifier.PRE_STATE_LABEL, e0, pve, v)(Q)

      case old @ ast.LabelledOld(e0, lbl) =>
        s.oldHeaps.get(lbl) match {
          case None =>
            Failure(pve dueTo LabelledStateNotReached(old))
          case Some(h) =>
            evalInOldState(s, lbl, e0, pve, v)(Q)}

      case ast.Let(x, e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1.copy(g = s1.g + (x.localVar, t0)), e1, pve, v1)(Q))

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => And(t1, t2), pve, v)(Q)

      /* Short-circuiting evaluation of AND */
      case ast.And(e0, e1) =>
        /* Evaluate `e0 && e1` as `e0 && (e0 ==> e1)`, but without evaluating `e0` twice */
        eval(s, e0, pve, v)((s1, t0, v1) => {
          val lv = ast.LocalVar(v1.identifierFactory.fresh("v").name)(e0.typ, e0.pos, e0.info)
          val e1Short = ast.Implies(lv, e1)(e1.pos, FromShortCircuitingAnd)
          eval(s1.copy(g = s1.g + (lv, t0)), e1Short, pve, v1)((s2, t1, v2) =>
            Q(s2, And(t0, t1), v2))})

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => Or(t1, t2), pve, v)(Q)

      /* Short-circuiting evaluation of OR */
      case ast.Or(e0, e1) =>
        /* Evaluate `e0 || e1` as `e0 || (!e0 && e1)`, but without evaluating `e0` twice */
        eval(s, e0, pve, v)((s1, t0, v1) => {
          val lv = ast.LocalVar(v1.identifierFactory.fresh("v").name)(e0.typ, e0.pos, e0.info)
          val e1Short = ast.And(ast.Not(lv)(e0.pos, e0.info), e1)(e1.pos, e1.info)
          eval(s1.copy(g = s1.g + (lv, t0)), e1Short, pve, v1)((s2, t1, v2) =>
            Q(s2, Or(t0, t1), v2))})

      case implies @ ast.Implies(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          evalImplies(s1, t0, e1, implies.info == FromShortCircuitingAnd, pve, v1)(Q))

      case ast.CondExp(e0, e1, e2) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) =>
            brancher.branch(s2, t0, v2)(
              (s3, v3) => eval(s3, e1, pve, v3)(QB),
              (s3, v3) => eval(s3, e2, pve, v3)(QB))
          )(entries => {
            /* TODO: The next few lines could be made safer if branch(...) took orElse-continuations
             *       that are executed if a branch is dead */
            val (s2, t1, t2) = entries match {
              case Seq(entry) if entry.pathConditions.branchConditions.head == t0 =>
                val t2 = v1.decider.appliedFresh("$deadElse", v1.symbolConverter.toSort(e2.typ), s1.relevantQuantifiedVariables)
                (entry.s, entry.data, t2)
              case Seq(entry) if entry.pathConditions.branchConditions.head == Not(t0) =>
                val t1 = v1.decider.appliedFresh("$deadThen", v1.symbolConverter.toSort(e1.typ), s1.relevantQuantifiedVariables)
                (entry.s, t1, entry.data)
              case Seq(entry1, entry2) =>
                (entry1.s.merge(entry2.s), entry1.data, entry2.data)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, Ite(t0, t1, t2))
          })(Q))

      /* Integers */

      case ast.Add(e0, e1) =>
        evalBinOp(s, e0, e1, Plus, pve, v)(Q)

      case ast.Sub(e0, e1) =>
        evalBinOp(s, e0, e1, Minus, pve, v)(Q)

      case ast.Mul(e0, e1) =>
        evalBinOp(s, e0, e1, Times, pve, v)(Q)

      case ast.Div(e0, e1) =>
        evalBinOp(s, e0, e1, Div, pve, v)((s1, tDiv, v1) =>
          failIfDivByZero(s1, tDiv, e1, tDiv.p1, 0, pve, v1)(Q))

      case ast.Mod(e0, e1) =>
        evalBinOp(s, e0, e1, Mod, pve, v)((s1, tMod, v1) =>
          failIfDivByZero(s1, tMod, e1, tMod.p1, 0, pve, v1)(Q))

      case ast.LeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)(Q)

      case ast.LtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)(Q)

      case ast.GeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)(Q)

      case ast.GtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)(Q)

      /* Permissions */

      case ast.PermAdd(e0, e1) =>
        evalBinOp(s, e0, e1, PermPlus, pve, v)(Q)

      case ast.PermSub(e0, e1) =>
        evalBinOp(s, e0, e1, PermMinus, pve, v)(Q)

      case ast.PermMinus(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, PermMinus(NoPerm(), t0), v1))

      case ast.PermMul(e0, e1) =>
        evalBinOp(s, e0, e1, PermTimes, pve, v)(Q)

      case ast.IntPermMul(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, v2) =>
            Q(s2, IntPermTimes(t0, t1), v2)))

      case ast.PermDiv(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, v2) =>
            failIfDivByZero(s2, PermIntDiv(t0, t1), e1, t1, 0, pve, v2)(Q)))

      case ast.PermLeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)(Q)

      case ast.PermLtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)(Q)

      case ast.PermGeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)(Q)

      case ast.PermGtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)(Q)

      /* Others */

      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = v1.symbolConverter.toSort(dfa.typ)
          val fi = v1.symbolConverter.toFunction(Verifier.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(s1, App(fi, tArgs), v1)})

      case ast.CurrentPerm(locacc) =>
        val h = s.partiallyConsumedHeap.getOrElse(s.h)
        evalLocationAccess(s, locacc, pve, v)((s1, name, args, v1) => {
          val loc = locacc.loc(Verifier.program)
          /* It is assumed that, for a given field/predicate identifier (loc)
           * either only quantified or only non-quantified chunks are used.
           */
          val usesQPChunks = loc match {
            case field: ast.Field => s1.qpFields.contains(field)
            case pred: ast.Predicate => s1.qpPredicates.contains(pred)}
          val perm =
            if (usesQPChunks) {
              loc match {
                case _: ast.Field =>
                  val chs = h.values.collect { case ch: QuantifiedFieldChunk if ch.id.name == name => ch }
                  val perm =
                    chs.foldLeft(NoPerm(): Term)((q, ch) =>
                      PermPlus(q, ch.perm.replace(`?r`, args.head)))
                  /* TODO: Try again once Silicon fully supports field accesses as triggers.
                   *       Currently, adding these axioms makes several of the RSL examples
                   *       exhibit matching loops (potentially other examples as well).
                   */
//                  v1.decider.prover.comment(s"perm($locacc)  ~~>  assume upper permission bound")
//                  v1.decider.prover.comment(perm.toString)
//                  v1.decider.assume(PermAtMost(perm, FullPerm()))
                  perm
                case pred: ast.Predicate =>
//                  //added for quantified predicate permissions
                  val formalArgs:Seq[Var] =
                    pred.formalArgs.map(formalArg => Var(Identifier(formalArg.name), v1.symbolConverter.toSort(formalArg.typ)))
                  val chs = h.values.collect { case ch: QuantifiedPredicateChunk if ch.id.name == name => ch }
                  chs.foldLeft(NoPerm(): Term)((q, ch) =>
                    PermPlus(q, ch.perm.replace(formalArgs, args)))
              }
            } else {
              val chs = chunkSupporter.findChunksWithID[BasicChunk](h.values, BasicChunkIdentifier(name))
              val perm =
                chs.foldLeft(NoPerm(): Term)((q, ch) => {
                  val argsPairWiseEqual = And(args.zip(ch.args).map{case (a1, a2) => a1 === a2})
                  PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm()))})
              /* TODO: See todo above */
//              v1.decider.prover.comment(s"perm($locacc)  ~~>  assume upper permission bound")
//              v1.decider.prover.comment(perm.toString)
//              v1.decider.assume(PermAtMost(perm, FullPerm()))
              perm
            }
          Q(s1, perm, v1)})

      case ast.ForPerm(varDecl, accessList, body) =>
        val qvar = varDecl.localVar
        /* Iterate over the list of relevant chunks in continuation passing style (very similar
         * to evals), and evaluate the forperm-body with a different qvar assignment each time.
         */
        def bindRcvrAndEvalBody(s: State,
                                chs: Iterable[BasicChunk],
                                ts: Seq[Term],
                                v: Verifier)
                               (Q: (State, Seq[Term], Verifier) => VerificationResult)
                               : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, v)
          else {
            val ch = chs.head
            val rcvr = ch.args.head /* NOTE: If ch is a predicate chunk, only the first argument is used */
            evalImplies(s.copy(s.g + (qvar, rcvr)), IsPositive(ch.perm), body, false, pve, v)((s1, tImplies, v1) =>
              bindRcvrAndEvalBody(s1, chs.tail, tImplies +: ts, v1)(Q))}
        }
        val s1 = s.copy(h = s.partiallyConsumedHeap.getOrElse(s.h))
        val locs = accessList.map(_.name)
        val chs = s1.h.values.collect { case ch: BasicChunk if locs contains ch.id.name => ch }
        bindRcvrAndEvalBody(s1, chs, Seq.empty, v)((s2, ts, v1) => {
          val s3 = s2.copy(h = s.h, g = s.g)
          Q(s3, And(ts), v1)})

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            /* It is expected that quantifiers have already been provided with triggers,
             * either explicitly or by using a trigger generator.
             */
            (forall, Forall, forall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, Seq())
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }

        val body = eQuant.exp
        val name = s"prog.l${viper.silicon.utils.ast.sourceLine(sourceQuant)}"
        evalQuantified(s, qantOp, eQuant.variables, Nil, Seq(body), Some(eTriggers), name, pve, v){
          case (s1, tVars, _, Seq(tBody), tTriggers, (tAuxGlobal, tAux), v1) =>
            v1.decider.prover.comment("Nested auxiliary terms: globals")
            v1.decider.assume(tAuxGlobal)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals")
            v1.decider.assume(tAux)
            val tQuant = Quantification(qantOp, tVars, tBody, tTriggers, name)
            Q(s1, tQuant, v1)}

      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val pvePre = PreconditionInAppFalse(fapp)
        val func = Verifier.program.findFunction(funcName)
        evals2(s, eArgs, Nil, _ => pve, v)((s1, tArgs, v1) => {
//          bookkeeper.functionApplications += 1
          val pre = func.pres map (pre => {
            /* Substitute actual for formal arguments in preconditions.
             * However, doing this naively can result in invalid triggers.
             * Consider the following example
             *
             *   function fun1(a: Int): Bool
             *     requires forall b: Int {fun2(a, b)} ...
             *
             *   // client
             *     assume fun1(x > y ? 1 : -1)
             *
             * where replacing `a` with `x > y ? 1 : -1` would yield an invalid trigger.
             *
             * For now, we simply remove all triggers that directly occur in the precondition.
             * This is OK because the precondition is consumed (exhaled), and forall-triggers are
             * therefore not relevant (and we don't yet support exists-triggers).
             *
             * However, this will not prevent prevent generating invalid triggers for quantifiers
             * that only indirectly occur in the precondition, e.g. when unfolding a predicate
             * instance in the precondition whose body contains a quantifier.
             *
             * See also https://bitbucket.org/viperproject/silicon/issues/276/.
             */
            val triggerFreePre = pre.transform{case q: ast.Forall => q.copy(triggers = Nil)(q.pos, q.info, q.errT)}
            ast.utility.Expressions.instantiateVariables(triggerFreePre, func.formalArgs, eArgs)
          })
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
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) => {
            val s3 = s2.copy(recordVisited = true,
                             smDomainNeeded = true)
            consumes(s3, pre, _ => pvePre, v2)((s4, snap, v3) => {
              val snap1 = snap.convert(sorts.Snap)
              val tFApp = App(v3.symbolConverter.toFunction(func), snap1 :: tArgs)
              val s5 = s4.copy(h = s2.h,
                               recordVisited = s2.recordVisited,
                               functionRecorder = s4.functionRecorder.recordSnapshot(fapp, v3.decider.pcs.branchConditions, snap1),
                               smDomainNeeded = s2.smDomainNeeded)
              QB(s5, tFApp, v3)})
            /* TODO: The join-function is heap-independent, and it is not obvious how a
             *       joined snapshot could be defined and represented
             */
            })(join(v1.symbolConverter.toSort(func.typ), s"joined_${func.name}", joinFunctionArgs, v1))(Q)})

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = Verifier.program.findPredicate(predicateName)
        if (s.cycles(predicate) < Verifier.config.recursivePredicateUnfoldings()) {
          evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
            eval(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
              v2.decider.assert(IsNonNegative(tPerm)) {
                case true =>
                  joiner.join[Term, Term](s2, v2)((s3, v3, QB) => {
                    val s4 = s3.incCycleCounter(predicate)
                               .copy(recordVisited = true)
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                      predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                        val c4 = c3.decCycleCounter(predicate)
//                        eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                          QB(tIn, c5))})
                    consume(s4, acc, pve, v3)((s5, snap, v4) => {
                      val s6 = s5.copy(functionRecorder = s5.functionRecorder.recordSnapshot(pa, v4.decider.pcs.branchConditions, snap),
                                       constrainableARPs = s1.constrainableARPs)
                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      v4.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
//                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                      val body = pa.predicateBody(Verifier.program).get /* Only non-abstract predicates can be unfolded */
                      val s7 = s6.scalePermissionFactor(tPerm)
                      produce(s7 /*\ insγ*/, toSf(snap), body, pve, v4)((s8, v5) => {
                        val s9 = s8.copy(recordVisited = s3.recordVisited,
                                          permissionScalingFactor = s6.permissionScalingFactor)
                                   .decCycleCounter(predicate)
                        eval(s9, eIn, pve, v5)(QB)})})
                  })(join(v2.symbolConverter.toSort(eIn.typ), "joinedIn", s2.relevantQuantifiedVariables, v2))(Q)
                case false =>
                  Failure(pve dueTo NegativePermission(ePerm))}))
        } else {
          val unknownValue = v.decider.appliedFresh("recunf", v.symbolConverter.toSort(eIn.typ), s.relevantQuantifiedVariables)
          Q(s, unknownValue, v)
        }

      case ast.Applying(wand, eIn) =>
        joiner.join[Term, Term](s, v)((s1, v1, QB) =>
          magicWandSupporter.applyWand(s1, wand, pve, v1)((s2, v2) => {
            eval(s2, eIn, pve, v2)(QB)
        }))(join(v.symbolConverter.toSort(eIn.typ), "joinedIn", s.relevantQuantifiedVariables, v))(Q)

      /* Sequences */

      case ast.SeqContains(e0, e1) => evalBinOp(s, e1, e0, SeqIn, pve, v)(Q)
        /* Note the reversed order of the arguments! */

      case ast.SeqIndex(e0, e1) =>
        evals2(s, Seq(e0, e1), Nil, _ => pve, v)({case (s1, Seq(t0, t1), v1) =>
          v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
            case true =>
              v1.decider.assert(Less(t1, SeqLength(t0))) {
                case true =>
                  Q(s1, SeqAt(t0, t1), v1)
                case false =>
                  Failure(pve dueTo SeqIndexExceedsLength(e0, e1))}
            case false =>
              Failure(pve dueTo SeqIndexNegative(e0, e1))
          }})

      case ast.SeqAppend(e0, e1) => evalBinOp(s, e0, e1, SeqAppend, pve, v)(Q)
      case ast.SeqDrop(e0, e1) => evalBinOp(s, e0, e1, SeqDrop, pve, v)(Q)
      case ast.SeqTake(e0, e1) => evalBinOp(s, e0, e1, SeqTake, pve, v)(Q)
      case ast.SeqLength(e0) => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, SeqLength(t0), v1))
      case ast.EmptySeq(typ) => Q(s, SeqNil(v.symbolConverter.toSort(typ)), v)
      case ast.RangeSeq(e0, e1) => evalBinOp(s, e0, e1, SeqRanged, pve, v)(Q)

      case ast.SeqUpdate(e0, e1, e2) =>
        evals2(s, List(e0, e1, e2), Nil, _ => pve, v)((s1, ts, v1) =>
          Q(s1, SeqUpdate(ts.head, ts(1), ts(2)), v1))

      case ast.ExplicitSeq(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(tSeq, SeqSingleton(te)))
          v1.decider.assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(s1, tSeq, v1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) => Q(s, EmptySet(v.symbolConverter.toSort(typ)), v)
      case ast.EmptyMultiset(typ) => Q(s, EmptyMultiset(v.symbolConverter.toSort(typ)), v)

      case ast.ExplicitSet(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(s1, tSet, v1)})

      case ast.ExplicitMultiset(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(s1, tMultiset, v1)})

      case ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetUnion, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetUnion, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIntersection, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetIntersection, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetSubset, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetSubset, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetDifference, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetDifference, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIn, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, (t0, t1) => MultisetCount(t1, t0), pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.SetType => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, SetCardinality(t0), v1))
        case _: ast.MultisetType => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, MultisetCardinality(t0), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }

      /* Unexpected nodes */

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(e))
    }

    resultTerm
  }

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp], /* Are evaluated and added as path conditions before ...*/
                     es2: Seq[ast.Exp], /* ... these terms are evaluated */
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Verifier) => VerificationResult)
                    : VerificationResult = {

    val localVars = vars map (_.localVar)

    val tVars = localVars map (x => v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ)))
    val gVars = Store(localVars zip tVars)
    val s1 = s.copy(g = s.g + gVars,
                    quantifiedVariables = tVars ++ s.quantifiedVariables,
                    recordPossibleTriggers = true,
                    possibleTriggers = Map.empty) // TODO: Why reset possibleTriggers if they are merged with s.possibleTriggers later anyway?
    type R = (State, Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Map[ast.Exp, Term])
    executionFlowController.locallyWithResult[R](s1, v)((s2, v1, QB) => {
       val preMark = v1.decider.setPathConditionMark()
      evals(s2, es1, _ => pve, v1)((s3, ts1, v2) => {
        val bc = And(ts1)
        v2.decider.setCurrentBranchCondition(bc)
        evals(s3, es2, _ => pve, v2)((s4, ts2, v3) => {
          evalTriggers(s4, optTriggers.getOrElse(Nil), pve, v3)((s5, tTriggers, v4) => { // TODO: v4 isn't forward - problem?
            val (auxGlobalQuants, auxNonGlobalQuants) =
              v3.decider.pcs.after(preMark).quantified(quant, tVars, tTriggers, s"$name-aux", isGlobal = false, bc)
            val additionalPossibleTriggers: Map[ast.Exp, Term] =
              if (s.recordPossibleTriggers) s5.possibleTriggers else Map()
            QB((s5, ts1, ts2, tTriggers, (auxGlobalQuants, auxNonGlobalQuants), additionalPossibleTriggers))})})})
    }){case (s2, ts1, ts2, tTriggers, auxQuant, additionalPossibleTriggers) =>
      val s3 = s.copy(possibleTriggers = s.possibleTriggers ++ additionalPossibleTriggers)
                .preserveAfterLocalEvaluation(s2)
      Q(s3, tVars, ts1, ts2, tTriggers, auxQuant, v)
    }
  }

  private def evalImplies(s: State,
                          tLhs: Term,
                          eRhs: ast.Exp,
                          fromShortCircuitingAnd: Boolean,
                          pve: PartialVerificationError,
                          v: Verifier)
                         (Q: (State, Term, Verifier) => VerificationResult)
                         : VerificationResult = {

    joiner.join[Term, Term](s, v)((s1, v1, QB) =>
      brancher.branch(s1, tLhs, v1, fromShortCircuitingAnd)(
        (s2, v2) => eval(s2, eRhs, pve, v2)(QB),
        (s2, v2) => QB(s2, True(), v2))
    )(entries => {
      assert(entries.length <= 2)
      val s1 = entries.tail.foldLeft(entries.head.s)((sAcc, entry) => sAcc.merge(entry.s))
      val t = Implies(tLhs, entries.headOption.map(_.data).getOrElse(True()))
      (s1, t)
    })(Q)
  }

  private def evalInOldState(s: State,
                             label: String,
                             e: ast.Exp,
                             pve: PartialVerificationError,
                             v: Verifier)
                            (Q: (State, Term, Verifier) => VerificationResult)
                            : VerificationResult = {

    val h = s.oldHeaps(label)
    val s1 = s.copy(h = h, partiallyConsumedHeap = None)
    val s2 = stateConsolidator.consolidateIfRetrying(s1, v)

    eval(s2, e, pve, v)((s3, t, v1) => {
      val s4 = s3.copy(h = s.h,
                       oldHeaps = s3.oldHeaps + (label -> s3.h),
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s4, t, v1)})
  }

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult = {

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          Q(s1, field.name, tRcvr :: Nil, v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          Q(s1, predicateName, tArgs, v1))
    }
  }

  private def evalBinOp[T <: Term]
                       (s: State,
                        e0: ast.Exp,
                        e1: ast.Exp,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
                        v: Verifier)
                       (Q: (State, T, Verifier) => VerificationResult)
                       : VerificationResult = {

    eval(s, e0, pve, v)((s1, t0, v1) =>
      eval(s1, e1, pve, v1)((s2, t1, v2) =>
        Q(s2, termOp(t0, t1), v2)))
  }

  private def failIfDivByZero(s: State,
                              t: Term,
                              eDivisor: ast.Exp,
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              v: Verifier)
                             (Q: (State, Term, Verifier) => VerificationResult)
                             : VerificationResult = {

    v.decider.assert(tDivisor !== tZero){
      case true => Q(s, t, v)
      case false => Failure(pve dueTo DivisionByZero(eDivisor))
    }
  }

  private def evalTriggers(s: State,
                           silverTriggers: Seq[ast.Trigger],
                           pve: PartialVerificationError,
                           v: Verifier)
                          (Q: (State, Seq[Trigger], Verifier) => VerificationResult)
                          : VerificationResult = {

    evalTriggers(s, silverTriggers map (_.exps), Nil, pve, v)((s1, tTriggersSets, v1) => {
      /* [2015-12-15 Malte]
       *   Evaluating triggers that did not occur in the body (and whose corresponding term has
       *   therefore not already been recorded in the context) might introduce new path conditions,
       *   in particular, new constants/functions and their definitions.
       *   This is, for example, the case in issue_0147.sil: the trigger generator can potentially
       *   replace the arithmetic expression `j+1` by a fresh, quantified variable (in the trigger,
       *   not necessarily in the quantifier body). Since it is part of the receiver of a quantified
       *   field dereference, the trigger mentioning the fresh variable might only be evaluated when
       *   evaluating the triggers, potentially leading to a newly introduced field value function.
       *
       *   TODO: Currently, new path conditions introduced while evaluating triggers will not be
       *         added to the auxiliary quantifier, i.e. they will not survive when the scope in
       *         which the quantifier (resp., its body and its triggers) is evaluated.
       *         Using such effectively "undefined" symbols in triggers will most likely result in
       *         incompletenesses because the corresponding quantifiers will not be triggered.
       */

      Q(s1, tTriggersSets map Trigger, v1)})
  }

  /** Evaluates the given list of trigger sets `eTriggerSets` (expressions) and passes the result
    * plus the initial trigger sets `tTriggerSets` (terms) to the continuation `Q`.
    */
  private def evalTriggers(s: State,
                           eTriggerSets: TriggerSets[ast.Exp],
                           tTriggersSets: TriggerSets[Term],
                           pve: PartialVerificationError,
                           v: Verifier)
                          (Q: (State, TriggerSets[Term], Verifier) => VerificationResult)
                          : VerificationResult = {

    if (eTriggerSets.isEmpty)
      Q(s, tTriggersSets, v)
    else
      evalTrigger(s, eTriggerSets.head, pve, v)((s1, ts, v1) =>
        evalTriggers(s1, eTriggerSets.tail, tTriggersSets :+ ts, pve, v1)(Q))
  }

  private def evalTrigger(s: State, exps: Seq[ast.Exp], pve: PartialVerificationError, v: Verifier)
                         (Q: (State, Seq[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    val (cachedTriggerTerms, remainingTriggerExpressions) =
      exps.map {
        case ast.Old(e) => e /* TODO: What about heap-dependent functions under old in triggers? */
        case e => e
      }.map {
        case fapp: ast.FuncApp =>
          /** Heap-dependent functions that are used as tTriggerSets should be used
            * in the limited version, because it allows for more instantiations.
            * Keep this code in sync with [[viper.silicon.supporters.ExpressionTranslator.translate]]
            *
            */
          val cachedTrigger =
            s.possibleTriggers.get(fapp) map {
              case app @ App(fun: HeapDepFun, _) =>
                app.copy(applicable = functionSupporter.limitedVersion(fun))
              case app: App =>
                app
              case other =>
                sys.error(s"Expected $fapp to map to a function application, but found $other")
            }

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(fapp))

        case pt @ (_: ast.PossibleTrigger | _: ast.FieldAccess) =>
          val cachedTrigger = s.possibleTriggers.get(pt)

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
    val preMark = v.decider.setPathConditionMark()
    var πDelta = InsertionOrderedSet.empty[Term]

    /* TODO: Evaluate as many remaining expressions as possible, i.e. don't
     *       stop if evaluating one fails
     *
     *       Here is an example where evaluating remainingTriggerExpressions will
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

    /* TODO: Use executionFlowController.locally instead of val r = ...; r && { ... }.
     *       This is currently not possible because executionFlowController.locally will only
     *       continue after the local block if the block was successful (i.e. if it yielded
     *       Success()). However, here we want to continue in any case.
     */

    val r =
      evals(s, remainingTriggerExpressions, _ => pve, v)((_, remainingTriggerTerms, v1) => {
        optRemainingTriggerTerms = Some(remainingTriggerTerms)
        πDelta = v1.decider.pcs.after(preMark).assumptions //decider.π -- πPre
        Success()})

    (r, optRemainingTriggerTerms) match {
      case (Success(), Some(remainingTriggerTerms)) =>
        v.decider.assume(πDelta)
        Q(s, cachedTriggerTerms ++ remainingTriggerTerms, v)
      case _ =>
//        bookkeeper.logfiles("evalTrigger").println(s"Couldn't evaluate some trigger expressions:\n  $remainingTriggerExpressions\nReason:\n  $r")
        Q(s, cachedTriggerTerms, v)
    }
  }

//  private def partiallyAppliedFresh(id: String, appliedArgs: Seq[Term], result: ast.Type, v: Verifier) = {
//    val appliedSorts = appliedArgs.map(_.sort)
//    val func = v.decider.fresh(id, appliedSorts, v.symbolConverter.toSort(result))
//
//    App(func, appliedArgs)
//  }

  private def join(joinSort: Sort,
                   joinFunctionName: String,
                   joinFunctionArgs: Seq[Term],
                   v: Verifier)
                  (entries: Seq[JoinDataEntry[Term]])
                  : (State, Term) = {

    assert(entries.nonEmpty, "Expected at least one join data entry")

    entries match {
      case Seq(entry) if entry.pathConditions.branchConditions.isEmpty =>
        (entry.s, entry.data)
      case _ =>
        val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
        val joinSymbol = v.decider.fresh(joinFunctionName, quantifiedVarsSorts, joinSort)
        val joinTerm = App(joinSymbol, joinFunctionArgs)

        val joinDefEqs = entries map (entry =>
          Implies(And(entry.pathConditions.branchConditions), joinTerm === entry.data))

        val sJoined = entries.tail.foldLeft(entries.head.s)((sAcc, entry) =>sAcc.merge(entry.s))

        v.decider.assume(joinDefEqs)

        (sJoined, joinTerm)
    }
  }

  private[silicon] case object FromShortCircuitingAnd extends Info {
    val comment = Nil
  }
}
