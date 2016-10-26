/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

import org.slf4s.Logging
import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.PreconditionInAppFalse
import viper.silver.verifier.reasons._
import viper.silicon.reporting.Bookkeeper
import viper.silicon.interfaces._
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.decider.Decider
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.implicits._
import viper.silicon.state.terms.perms.IsNonNegative
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters._
import viper.silicon.supporters.qps.{SummarisingFvfDefinition, QuantifiedChunkSupporter}
import viper.silicon.supporters.functions.FunctionSupporter

trait DefaultEvaluator[ST <: Store[ST],
                       H <: Heap[H],
                       S <: State[ST, H, S]]
    extends Evaluator[ST, H, S, DefaultContext[H]]
    { this: Logging with Consumer[ST, H, S, DefaultContext[H]]
                    with Producer[ST, H, S, DefaultContext[H]]
                    with Brancher[ST, H, S, DefaultContext[H]]
                    with Joiner[DefaultContext[H]]
                    with MagicWandSupporter[ST, H, S] =>

  private[this] type C = DefaultContext[H]

  protected val decider: Decider[ST, H, S, C]
  protected val stateFactory: StateFactory[ST, H, S]
  protected val symbolConverter: SymbolConvert
  protected val stateFormatter: StateFormatter[ST, H, S, String]
  protected val config: Config
  protected val bookkeeper: Bookkeeper
  protected val heapCompressor: HeapCompressor[ST, H, S, C]
  protected val predicateSupporter: PredicateSupporter[ST, H, S, C]
  protected val quantifiedChunkSupporter: QuantifiedChunkSupporter[ST, H, S, C]
  protected val chunkSupporter: ChunkSupporter[ST, H, S, C]

  import decider.{fresh, assume}
  import stateFactory._
  import symbolConverter.toSort

  def evals(σ: S, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, c: C)
           (Q: (List[Term], C) => VerificationResult)
           : VerificationResult =

    evals2(σ, es, Nil, pvef, c)(Q)

  private def evals2(σ: S, es: Seq[ast.Exp], ts: List[Term], pvef: ast.Exp => PartialVerificationError, c: C)
                    (Q: (List[Term], C) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(ts.reverse, c)
    else
      eval(σ, es.head, pvef(es.head), c)((t, c1) =>
        evals2(σ, es.tail, t :: ts, pvef, c1)(Q))
  }

  /** Wrapper Method for eval, for logging. See Executor.scala for explanation of analogue. **/
  def eval(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
          (Q: (Term, C) => VerificationResult)
          : VerificationResult = {
    val sepIdentifier = SymbExLogger.currentLog().insert(new EvaluateRecord(e, σ, decider.π, c.asInstanceOf[DefaultContext[ListBackedHeap]]))
    eval3(σ, e, pve, c)((e1, c1) => {
      SymbExLogger.currentLog().collapse(e, sepIdentifier)
      Q(e1, c1)})
  }

  def eval3(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
           (Q: (Term, C) => VerificationResult)
  : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
            | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
            | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        log.debug(s"\nEVAL ${utils.ast.sourceLineColumn(e)}: $e")
        log.debug(stateFormatter.format(σ, decider.π))
        if (c.reserveHeaps.nonEmpty)
          log.debug("hR = " + c.reserveHeaps.map(stateFormatter.format).mkString("", ",\n     ", ""))
        c.lhsHeap.foreach(h => log.debug("hLHS = " + stateFormatter.format(h)))
        decider.prover.logComment(s"[eval] $e")
    }

    /* Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * Also deactivate magic wand's recording of consumed and produced permissions: if the
     * evaluation to perform involves consuming or producing permissions, e.g. because of
     * an unfolding expression, these should not be recorded.
     */
    val σ1 = σ \ magicWandSupporter.getEvalHeap(σ, c)
    val c1 = c.copy(reserveHeaps = Nil, exhaleExt = false, recordEffects = false)

    eval2(σ1, e, pve, c1)((t, c2) => {
      val c3 =
        if (c2.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger =>
              c2.copy(possibleTriggers = c2.possibleTriggers + (pt -> t))
            case fa: ast.FieldAccess if c2.qpFields.contains(fa.field) =>
              c2.copy(possibleTriggers = c2.possibleTriggers + (fa -> t))
            case _ =>
              c2}
        else
          c2
      val c4 = c3.copy(reserveHeaps = c.reserveHeaps, exhaleExt = c.exhaleExt, recordEffects = c.recordEffects)
      Q(t, c4)})
  }

  protected def eval2(σ: S, e: ast.Exp, pve: PartialVerificationError, c: C)
                     (Q: (Term, C) => VerificationResult)
                     : VerificationResult = {

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

      case fa: ast.FieldAccess if c.qpFields.contains(fa.field) =>
        eval(σ, fa.rcv, pve, c)((tRcvr, c1) => {
          val (quantifiedChunks, _) = quantifiedChunkSupporter.splitHeap(σ.h, fa.field.name)
          c1.fvfCache.get((fa.field, quantifiedChunks)) match { /* TOOD: Drop field from cache map, quantifiedChunks should suffice */
            case Some(fvfDef: SummarisingFvfDefinition) if !config.disableValueMapCaching() =>
              /* The next assertion must be made if the FVF definition is taken from the cache;
               * in the other case it is part of quantifiedChunkSupporter.withValue.
               */
              decider.assert(σ, PermLess(NoPerm(), fvfDef.totalPermissions(tRcvr))) {
                case false =>
                  Failure(pve dueTo InsufficientPermission(fa))
                case true =>
                  assume(fvfDef.quantifiedValueDefinitions)
                    /* Re-emit definition since the previous definition could be nested under
                     * an auxiliary quantifier (resulting from the evaluation of some Silver
                     * quantifier in whose body field 'fa.field' was accessed)
                     * which is protected by a trigger term that we currently don't have.
                     */
                  val fvfLookup = Lookup(fa.field.name, fvfDef.fvf, tRcvr)
                  val fr1 = c1.functionRecorder.recordSnapshot(fa, decider.pcs.branchConditions, fvfLookup)
                  val c2 = c1.copy(functionRecorder = fr1)
                  Q(fvfLookup, c2)}
            case _ =>
              quantifiedChunkSupporter.withValue(σ, σ.h, fa.field, Nil, True(), tRcvr, pve, fa, c1)(fvfDef => {
                assume(fvfDef.quantifiedValueDefinitions)
                val fvfLookup = Lookup(fa.field.name, fvfDef.fvf, tRcvr)

                val fr1 = c1.functionRecorder.recordSnapshot(fa, decider.pcs.branchConditions, fvfLookup)
                                             .recordQPTerms(c1.quantifiedVariables, decider.pcs.branchConditions, /*fvfDomain ++ */fvfDef.quantifiedValueDefinitions)
                val fr2 = if (true/*fvfDef.freshFvf*/) fr1.recordFvf(fa.field, fvfDef.fvf) else fr1
                val c2 = c1.copy(functionRecorder = fr2,
                                 fvfCache = if (config.disableValueMapCaching()) c1.fvfCache else c1.fvfCache + ((fa.field, quantifiedChunks) -> fvfDef))
                Q(fvfLookup, c2)})}})

      case fa: ast.FieldAccess =>
        evalLocationAccess(σ, fa, pve, c)((name, args, c1) =>
          chunkSupporter.withChunk(σ, σ.h, name, args, None, fa, pve, c1)((ch, c2) => {
            val c3 = c2.copy(functionRecorder = c2.functionRecorder.recordSnapshot(fa, decider.pcs.branchConditions, ch.snap))
            Q(ch.snap, c3)}))

      case ast.Not(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Not(t0), c1))

      case ast.Minus(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(Minus(0, t0), c1))

      case ast.Old(e0) => evalOld(σ, σ.g, e0, pve, c)(Q)

      case old @ ast.LabelledOld(e0, lbl) =>
        c.oldHeaps.get(lbl) match {
          case None =>
            Failure(pve dueTo LabelledStateNotReached(old))
          case Some(h) =>
            evalOld(σ, h, e0, pve, c)(Q)}

      case ast.ApplyOld(e0) => eval(σ \ c.lhsHeap.get, e0, pve, c)(Q)

      case ast.Let(v, e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ \+ (v.localVar, t0), e1, pve, c1)((t1, c2) =>
            Q(t1, c2)))

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, (t1, t2) => And(t1, t2), pve, c)(Q)

      /* Short-circuiting evaluation of AND */
      case ast.And(e0, e1) =>
        /* TODO: Avoid evaluating e0 twice */
        val e1Short = ast.Implies(e0, e1)(e1.pos, e1.info)
        evalBinOp(σ, e0, e1Short, (t1, t2) => And(t1, t2), pve, c)(Q)

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if config.disableShortCircuitingEvaluations() =>
        evalBinOp(σ, e0, e1, (t1, t2) => Or(t1, t2), pve, c)(Q)

      /* Short-circuiting evaluation of OR */
      case ast.Or(e0, e1) =>
        /* TODO: Avoid evaluating e0 twice */
        val e1Short = ast.And(ast.Not(e0)(e0.pos, e0.info), e1)(e1.pos, e1.info)
        evalBinOp(σ, e0, e1Short, (t1, t2) => Or(t1, t2), pve, c)(Q)

      case ast.Implies(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          evalImplies(σ, t0, e1, pve, c1)(Q))
//          join[Term, Term](c1, QB =>
//            branch(σ, t0, c1,
//              (c2: C) => eval(σ, e1, pve, c2)(QB),
//              (c2: C) => QB(True(), c2))
//          )(entries => {
//            assert(entries.length <= 2)
//            Implies(t0, entries.headOption.map(_.data).getOrElse(True()))
//          })(Q))

      case ite @ ast.CondExp(e0, e1, e2) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          join[Term, Term](c1, QB =>
            branch(σ, t0, c1,
              (c2: C) => eval(σ, e1, pve, c2)(QB),
              (c2: C) => eval(σ, e2, pve, c2)(QB))
          )(entries => {
            val (t1, t2) = entries match {
              case Seq(entry) if entry.pathConditionStack.branchConditions.head == t0 =>
                (entry.data, partiallyAppliedFresh("$deadElse", c.quantifiedVariables, e2.typ))
              case Seq(entry) if entry.pathConditionStack.branchConditions.head == Not(t0) =>
                (partiallyAppliedFresh("$deadThen", c.quantifiedVariables, e1.typ), entry.data)
              case Seq(entry1, entry2) =>
                (entry1.data, entry2.data)
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            Ite(t0, t1, t2)
          })(Q))

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

      case ast.PermMinus(e0) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          Q(PermMinus(NoPerm(), t0), c1))

      case ast.PermMul(e0, e1) =>
        evalBinOp(σ, e0, e1, PermTimes, pve, c)(Q)

      case ast.IntPermMul(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            Q(IntPermTimes(t0, t1), c2)))

      case ast.PermDiv(e0, e1) =>
        eval(σ, e0, pve, c)((t0, c1) =>
          eval(σ, e1, pve, c1)((t1, c2) =>
            failIfDivByZero(σ, PermIntDiv(t0, t1), e1, t1, 0, pve, c2)(Q)))

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
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = toSort(dfa.typ)
          val fi = symbolConverter.toFunction(c.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(App(fi, tArgs), c1)})

      case ast.CurrentPerm(locacc) =>
        val h = c.partiallyConsumedHeap.getOrElse(σ.h)
        evalLocationAccess(σ, locacc, pve, c)((name, args, c1) => {
          val loc = locacc.loc(c1.program)
          /* It is assumed that, for a given field/predicate identifier (loc)
           * either only quantified or only non-quantified chunks are used.
           */
          val usesQPChunks = loc match {
            case field: ast.Field => c.qpFields.contains(field)
            case pred: ast.Predicate => c.qpPredicates.contains(pred)}
          val perm:Term =
            if (usesQPChunks) {
              loc match {
                case field: ast.Field =>
                  val chs = h.values.collect { case ch: QuantifiedFieldChunk if ch.name == name => ch }
                  chs.foldLeft(NoPerm(): Term)((q, ch) =>
                    PermPlus(q, ch.perm.replace(`?r`, args.head)))
                case pred: ast.Predicate =>
                  //added for quantified predicate permissions
                  var formalArgs:Seq[Var] = pred.formalArgs.map(formalArg => Var(Identifier(formalArg.name), toSort(formalArg.typ)))
                  val chs = h.values.collect { case ch: QuantifiedPredicateChunk if ch.name == name => ch }
                  chs.foldLeft(NoPerm(): Term)((q, ch) =>
                    PermPlus(q, ch.perm.replace(formalArgs, args)))}
            } else {
              val chs = h.values.collect { case ch: BasicChunk if ch.name == name => ch }
              chs.foldLeft(NoPerm(): Term)((q, ch) => {
                val argsPairWiseEqual = And(args.zip(ch.args).map{case (a1, a2) => a1 === a2})
                PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm()))})
            }
          Q(perm, c1)})

      case ast.ForPerm(varDecl, accessList, body) =>
        val σ1 = σ \ c.partiallyConsumedHeap.getOrElse(σ.h)
        val qvar = varDecl.localVar
        val locs = accessList.map(_.name)
        val chs = σ1.h.values.collect { case ch: BasicChunk if locs contains ch.name => ch }

        /* Iterate over the list of relevant chunks in continuation passing style (very similar
         * to evals), and evaluate the forperm-body with a different qvar assignment each time.
         */
        def bindRcvrAndEvalBody(chs: Iterable[BasicChunk],
                                ts: Seq[Term],
                                c: C)
                               (Q: (Seq[Term], C) => VerificationResult)
                               : VerificationResult = {
          if (chs.isEmpty)
            Q(ts.reverse, c)
          else {
            val ch = chs.head
            val rcvr = ch.args.head /* NOTE: If ch is a predicate chunk, only the first argument is used */
            evalImplies(σ1 \+ (qvar, rcvr), PermLess(NoPerm(), ch.perm), body, pve, c)((tImplies, c1) =>
              bindRcvrAndEvalBody(chs.tail, tImplies +: ts, c1)(Q))}
        }

        bindRcvrAndEvalBody(chs, Seq.empty, c)((ts, c1) =>
          Q(And(ts), c1))

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            val autoTriggeredForall = utils.ast.autoTrigger(forall, c.qpFields)
            (autoTriggeredForall, Forall, autoTriggeredForall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, Seq())
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }

        val body = eQuant.exp
        val vars = eQuant.variables map (_.localVar)
        val name = s"prog.l${utils.ast.sourceLine(sourceQuant)}"
        evalQuantified(σ, qantOp, vars, Nil, Seq(body), Some(eTriggers), name, pve, c){
          case (tVars, _, Seq(tBody), tTriggers, Right(tAuxQuants), c1) =>
            decider.prover.logComment("Nested auxiliary terms")
            assume(tAuxQuants)
            val tQuant = Quantification(qantOp, tVars, tBody, tTriggers, name)
            Q(tQuant, c1)}

      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val pvePre = PreconditionInAppFalse(fapp)
        val func = c.program.findFunction(funcName)

        evals2(σ, eArgs, Nil, _ => pve, c)((tArgs, c2) => {
          bookkeeper.functionApplications += 1
          val pre = func.pres map (ast.utility.Expressions.instantiateVariables(_, func.formalArgs, eArgs))
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
          join[Term, Term](c2, QB => {
            val c3 = c2.copy(recordVisited = true,
                             fvfAsSnap = true)
            consumes(σ, pre, _ => pvePre, c3)((_, s, c4) => {
              val s1 = s.convert(sorts.Snap)
              val tFApp = App(symbolConverter.toFunction(func), s1 :: tArgs)
              val c5 = c4.copy(recordVisited = c2.recordVisited,
//                               functionRecorder = c4.functionRecorder.recordSnapshot(fapp, c4.branchConditions, s1),
                               functionRecorder = c4.functionRecorder.recordSnapshot(fapp, decider.pcs.branchConditions, s1),
                               fvfAsSnap = c2.fvfAsSnap)
              /* TODO: Necessary? Isn't tFApp already recorded by the outermost eval? */
              val c6 = if (c5.recordPossibleTriggers) c5.copy(possibleTriggers = c5.possibleTriggers + (fapp -> tFApp)) else c5
              QB(tFApp, c6)})
            })(join(toSort(func.typ), s"joined_${func.name}", joinFunctionArgs))(Q)})

      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = c.program.findPredicate(predicateName)

        if (c.cycles(predicate) < config.recursivePredicateUnfoldings()) {
          evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
            eval(σ, ePerm, pve, c1)((tPerm, c2) =>
              decider.assert(σ, IsNonNegative(tPerm)) {
                case true =>
                  join[Term, Term](c2, QB => {
                    val c3 = c2.incCycleCounter(predicate)
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
                    consume(σ, acc, pve, c3)((σ1, snap, c4) => {
//                      val c5 = c4.copy(functionRecorder = c4.functionRecorder.recordSnapshot(pa, c4.branchConditions, snap))
                      val c5 = c4.copy(functionRecorder = c4.functionRecorder.recordSnapshot(pa, decider.pcs.branchConditions, snap))
                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      decider.assume(App(predicateSupporter.data(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
//                    val insγ = Γ(predicate.formalArgs map (_.localVar) zip tArgs)
                      val body = pa.predicateBody(c5.program).get /* Only non-abstract predicates can be unfolded */
                      val c5a = c5.scalePermissionFactor(tPerm)
                      produce(σ1 /*\ insγ*/, s => snap.convert(s), body, pve, c5a)((σ2, c6) => {
                        val c7 = c6.copy(recordVisited = c2.recordVisited,
                                          permissionScalingFactor = c5.permissionScalingFactor)
                                   .decCycleCounter(predicate)
                        val σ3 = σ2 //\ (g = σ.g)
                        eval(σ3 /*\ σ.γ*/, eIn, pve, c7)(QB)})})
                  })(join(toSort(eIn.typ), "joinedIn", c2.quantifiedVariables))(Q)
                case false =>
                  Failure(pve dueTo NegativePermission(ePerm))}))
        } else {
          val unknownValue = partiallyAppliedFresh("recunf", c.quantifiedVariables, eIn.typ)
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
        evals2(σ, List(e0, e1, e2), Nil, _ => pve, c)((ts, c1) =>
          Q(SeqUpdate(ts.head, ts(1), ts(2)), c1))

      case ast.ExplicitSeq(es) =>
        evals2(σ, es, Nil, _ => pve, c)((tEs, c1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(tSeq, SeqSingleton(te)))
          assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(tSeq, c1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) => Q(EmptySet(toSort(typ)), c)
      case ast.EmptyMultiset(typ) => Q(EmptyMultiset(toSort(typ)), c)

      case ast.ExplicitSet(es) =>
        evals2(σ, es, Nil, _ => pve, c)((tEs, c1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(tSet, c1)})

      case ast.ExplicitMultiset(es) =>
        evals2(σ, es, Nil, _ => pve, c)((tEs, c1) => {
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
        Failure(utils.consistency.createUnexpectedInhaleExhaleExpressionError(e))
    }

    resultTerm
  }

  def evalQuantified(σ: S,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVar],
                     es1: Seq[ast.Exp], /* Are evaluated and added as path conditions before ...*/
                     es2: Seq[ast.Exp], /* ... these terms are evaluated */
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     c: C)
                    (Q: (Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], Either[Quantification, Seq[Quantification]], C) => VerificationResult)
  : VerificationResult = {

    val tVars = vars map (v => fresh(v.name, toSort(v.typ)))
    val γVars = Γ(vars zip tVars)
    val σQuant = σ \+ γVars

    val c0 = c.copy(quantifiedVariables = tVars ++ c.quantifiedVariables,
      recordPossibleTriggers = true,
      possibleTriggers = Map.empty)

    decider.locally[(Seq[Term], Seq[Term], Seq[Trigger], Either[Quantification, Seq[Quantification]], C)](QB => {
      val preMark = decider.setPathConditionMark()
      evals(σQuant, es1, _ => pve, c0)((ts1, c1) => {
        val bc = And(ts1)
        decider.setCurrentBranchCondition(bc)
        evals(σQuant, es2, _ => pve, c1)((ts2, c2) => {
          val πDelta = decider.pcs.after(preMark).assumptions - bc
          evalTriggers(σQuant, optTriggers.getOrElse(Nil), πDelta, pve, c2)((tTriggers, c3) => {
            def auxQuantGen(trigger: Trigger, extraVars: Iterable[Var]) =
              Quantification(quant, tVars ++ extraVars, And(πDelta), Seq(trigger), s"$name-aux")
            val auxQuant =
              if (optTriggers.isEmpty)
                Left(auxQuantGen(Trigger(Nil), Nil))
              else {
                val triggersAndVars =
                  QuantifierSupporter.makeTriggersHeapIndependent(tTriggers, fresh)
                Right(triggersAndVars map {case (ts, vs) => auxQuantGen(ts, vs)})}
            val c4 = c3.copy(quantifiedVariables = c3.quantifiedVariables.drop(tVars.length),
              recordPossibleTriggers = c.recordPossibleTriggers,
              possibleTriggers = c.possibleTriggers ++ (if (c.recordPossibleTriggers) c3.possibleTriggers else Map()))
            QB(ts1, ts2, tTriggers, auxQuant, c4)})})})
    }){case (ts1, ts2, tTriggers, auxQuant, c1) =>
      Q(tVars, ts1, ts2, tTriggers, auxQuant, c1)
    }
  }


  def evalImplies(σ: S, tLhs: Term, eRhs: ast.Exp, pve: PartialVerificationError, c: C)
                 (Q: (Term, C) => VerificationResult)
                 : VerificationResult = {

    join[Term, Term](c, QB =>
      branch(σ, tLhs, c,
        (c1: C) => eval(σ, eRhs, pve, c1)(QB),
        (c1: C) => QB(True(), c1))
    )(entries => {
      assert(entries.length <= 2)
      Implies(tLhs, entries.headOption.map(_.data).getOrElse(True()))
    })(Q)
  }

  def evalOld(σ: S, h: H, e: ast.Exp, pve: PartialVerificationError, c: C)
             (Q: (Term, C) => VerificationResult)
             : VerificationResult =

    if (c.retrying) {
      /* See comment in DefaultDecider.tryOrFail */
      var originalChunks: Option[Iterable[Chunk]] = None
      def compressHeapIfRetrying(c: C, σ: S, h: H) {
        if (c.retrying) {
          originalChunks = Some(h.values)
          heapCompressor.compress(σ, h, c)
        }
      }
      def restoreHeapIfPreviouslyCompressed(h: H) {
        originalChunks match {
          case Some(chunks) => h.replace(chunks)
          case None => /* Nothing to do here */
        }
      }

      compressHeapIfRetrying(c, σ, h)
      val r =
        eval(σ \ h, e, pve, c.copy(partiallyConsumedHeap = None))((t, c1) =>
          Q(t, c1.copy(partiallyConsumedHeap = c.partiallyConsumedHeap)))
      restoreHeapIfPreviouslyCompressed(h)

      r
    } else
      eval(σ \ h, e, pve, c.copy(partiallyConsumedHeap = None))((t, c1) =>
        Q(t, c1.copy(partiallyConsumedHeap = c.partiallyConsumedHeap)))

  def evalLocationAccess(σ: S,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         c: C)
                        (Q: (String, Seq[Term], C) => VerificationResult)
                        : VerificationResult = {

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(σ, eRcvr, pve, c)((tRcvr, c1) =>
          Q(field.name, tRcvr :: Nil, c1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(σ, eArgs, _ => pve, c)((tArgs, c1) =>
          Q(predicateName, tArgs, c1))
    }
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
      case false => Failure(pve dueTo DivisionByZero(eDivisor))
    }
  }

  private def evalTriggers(σ: S,
                           silverTriggers: Seq[ast.Trigger],
                           bodyPathConditions: Set[Term],
                           pve: PartialVerificationError,
                           c: C)
                          (Q: (Seq[Trigger], C) => VerificationResult)
                          : VerificationResult = {

    evalTriggers(σ, silverTriggers map (_.exps), Nil, pve, c)((tTriggersSets, c1) => {
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

      Q(tTriggersSets map Trigger, c1)})
  }

  /** Evaluates the given list of trigger sets `eTriggerSets` (expressions) and passes the result
    * plus the initial trigger sets `tTriggerSets` (terms) to the continuation `Q`.
    */
  private def evalTriggers(σ: S,
                           eTriggerSets: TriggerSets[ast.Exp],
                           tTriggersSets: TriggerSets[Term],
                           pve: PartialVerificationError,
                           c: C)
                          (Q: (TriggerSets[Term], C) => VerificationResult)
                          : VerificationResult = {

    if (eTriggerSets.isEmpty)
      Q(tTriggersSets, c)
    else
      evalTrigger(σ, eTriggerSets.head, pve, c)((ts, c1) =>
        evalTriggers(σ, eTriggerSets.tail, tTriggersSets :+ ts, pve, c1)(Q))
  }

  private def evalTrigger(σ: S, exps: Seq[ast.Exp], pve: PartialVerificationError, c: C)
                         (Q: (Seq[Term], C) => VerificationResult)
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
            c.possibleTriggers.get(fapp) map {
              case app @ App(fun: HeapDepFun, _) =>
                app.copy(applicable = FunctionSupporter.limitedVersion(fun))
              case other =>
                sys.error(  s"Expected $fapp to map to an application of a heap-dependent function, "
                          + s"but found $other")
            }

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(fapp))

        case pt @ (_: ast.PossibleTrigger | _: ast.FieldAccess) =>
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
//    val πPre: Set[Term] = decider.π
    val preMark = decider.setPathConditionMark()
    var πDelta: Set[Term] = Set()

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

    /* TODO: Use Decider.locally instead of val r = ...; r && { ... }.
     *       This is currently not possible because Decider.locally will only continue after
     *       the local block if the block was successful (i.e. if it yielded Success()).
     *       However, here we want to continue in any case.
     */

    val r =
      evals(σ, remainingTriggerExpressions, _ => pve, c)((remainingTriggerTerms, c1) => {
        optRemainingTriggerTerms = Some(remainingTriggerTerms)
        πDelta = decider.pcs.after(preMark).assumptions //decider.π -- πPre
        Success()})

    (r, optRemainingTriggerTerms) match {
      case (Success(), Some(remainingTriggerTerms)) =>
        assume(πDelta)
        Q(cachedTriggerTerms ++ remainingTriggerTerms, c)
      case _ =>
        bookkeeper.logfiles("evalTrigger").println(s"Couldn't evaluate some trigger expressions:\n  $remainingTriggerExpressions\nReason:\n  $r")
        Q(cachedTriggerTerms, c)
    }
  }

  private def partiallyAppliedFresh(id: String, appliedArgs: Seq[Term], result: ast.Type) = {
    val appliedSorts = appliedArgs.map(_.sort)
    val func = decider.fresh(id, appliedSorts, toSort(result))

    App(func, appliedArgs)
  }

  private def join(joinSort: Sort,
                   joinFunctionName: String,
                   joinFunctionArgs: Seq[Term])
                  (entries: Seq[JoinDataEntry[C, Term]])
                  : Term = {

    assert(entries.nonEmpty, "Expected at least one join data entry")

//    println("\n[Evaluator.join]")
//    println("  entries = ")
//    entries foreach (e => println(s"  $e"))

    entries match {
//      case Seq(entry) if entry.newBranchConditions.isEmpty =>
      case Seq(entry) if entry.pathConditionStack.branchConditions.isEmpty =>
        entry.data
      case _ =>
        val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
        val joinSymbol = decider.fresh(joinFunctionName, quantifiedVarsSorts, joinSort)
        val joinTerm = App(joinSymbol, joinFunctionArgs)

        val joinDefEqs = entries map (entry =>
          Implies(And(entry.pathConditionStack.branchConditions), joinTerm === entry.data))

//        println(s"  joinTerm = $joinTerm")
//        println(s"  joinDefEqs = ")
//        joinDefEqs foreach (e => println(s"  $e"))

        decider.assume(joinDefEqs)

        joinTerm
    }
  }
}
