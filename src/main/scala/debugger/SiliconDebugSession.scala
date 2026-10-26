// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, RecordedPathConditions, Z3ProverStdIO}
import viper.silicon.interfaces.{Failure, SiliconDebuggingFailureContext, SiliconMappedCounterexample, Success, VerificationResult}
import viper.silicon.rules.{consumer, evaluator, executor}
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, True}
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.ast
import viper.silver.ast.{NoPosition, SourcePNodeInfo}
import viper.silver.parser._
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{ErrorReason, PartialVerificationError}
import viper.silver.verifier.errors.{AssertFailed, ContractNotWellformed}

import java.nio.file.Paths
import scala.collection.mutable

/**
  * A headless, I/O-free API for debugging a failed verification. All state of the debugger lives here; the
  * command-line frontend ([[SiliconDebuggerCli]]) and ViperServer's LSP integration are both thin clients of
  * this class.
  *
  * A session keeps the symbolic state and the verifier of the failed verification alive, so it must be closed
  * (via [[close]]) when it is no longer needed, otherwise prover processes and a considerable amount of memory
  * are leaked.
  *
  * This class is '''not''' thread-safe: it owns a prover process and a mutable symbolic state, so callers must
  * serialize all calls.
  */
class SiliconDebugSession(verificationResults: List[VerificationResult],
                          resolver: Option[Resolver],
                          pprogram: Option[PProgram],
                          translator: Option[Translator],
                          mainVerifier: MainVerifier,
                          val config: Config) {

  private val allFailures: List[Failure] =
    (verificationResults filter (_.isInstanceOf[Failure])) map (_.asInstanceOf[Failure])

  private var obl: Option[ProofObligation] = None
  private var originalObl: Option[ProofObligation] = None
  private var currentWorker: Option[WorkerVerifier] = None
  private var lastSolverOptions: Option[String] = None
  private var closed: Boolean = false

  /** The cases the last fold or unfold produced, if it branched: what distinguishes each, and its obligation. */
  private var cases: Seq[(String, ProofObligation)] = Seq.empty

  /** The model of the last failed proof attempt, if one is available; see [[CounterexampleModel]]. */
  private var counterexample: Option[CounterexampleModel] = None

  /** The parser used for expressions entered by the user; kept around since creating one is not cheap. */
  private lazy val debugParser: DebugParser = new DebugParser()

  // -------------------------------------------------------------------------------------------------------
  // Queries
  // -------------------------------------------------------------------------------------------------------

  def failures: Seq[DebugFailureInfo] = allFailures.zipWithIndex.map { case (f, idx) =>
    val reason = f.message.reason
    DebugFailureInfo(idx, reason.readableMessage, reason.pos.toString, DebugSourcePos.from(reason.pos),
      memberName(f), debuggable = debugContextOf(f).isDefined)
  }

  /**
    * The reason of each failure, in the same order as [[failures]].
    *
    * [[DebugFailureInfo]] renders positions and messages as strings, which is all a serialized protocol can carry.
    * A frontend running in the same JVM instead needs the Viper nodes themselves, because only those still carry
    * what it attached to them while translating its own source language.
    */
  def failureReasons: Seq[ErrorReason] = allFailures.map(_.message.reason)

  def hasDebuggableFailure: Boolean = allFailures.exists(f => debugContextOf(f).isDefined)

  def currentFailureIndex: Option[Int] = currentIndex

  def currentObligation: Option[ObligationModel] = obl.map(buildModel)

  /**
    * The obligation itself, rather than the string-only model of it.
    *
    * [[ObligationModel]] is deliberately free of Viper and Silicon types so that it can be serialized; a frontend
    * that runs in the same JVM (Nagini, for instance) instead needs the actual [[ast.Exp]] nodes, because only
    * those still carry the information it attached to them while translating its own source language.
    */
  def currentProofObligation: Option[ProofObligation] = obl

  def isClosed: Boolean = closed

  /**
    * Whether expressions can be entered as Viper source text. This requires the parser, resolver and translator of
    * the frontend that produced the program, which only exists if the program was parsed from Viper source. A
    * frontend that builds the [[viper.silver.ast.Program]] programmatically has none and must translate the user's
    * input itself, using [[addAssumptionExp]] and [[assertExp]].
    */
  def acceptsTextualExpressions: Boolean = resolver.isDefined && pprogram.isDefined && translator.isDefined

  private var currentIndex: Option[Int] = None

  private def buildModel(o: ProofObligation): ObligationModel =
    ObligationModelBuilder.build(o, currentIndex.getOrElse(0), lastSolverOptions)
      .copy(counterexample = counterexample)

  /** Whether the verification ran with counterexamples enabled; without that, the prover keeps no model. */
  def counterexamplesAvailable: Boolean = config.counterexample.toOption.isDefined

  /** Marks the current counterexample as no longer matching the assumptions. */
  private def invalidateCounterexample(): Unit =
    counterexample = counterexample.map(_.copy(stale = true))

  private def debugContextOf(f: Failure): Option[SiliconDebuggingFailureContext] =
    f.message.failureContexts.collectFirst { case c: SiliconDebuggingFailureContext => c }

  private def memberName(f: Failure): Option[String] =
    debugContextOf(f).flatMap(_.state).flatMap(_.currentMember).map(_.name)

  // -------------------------------------------------------------------------------------------------------
  // Commands
  // -------------------------------------------------------------------------------------------------------

  /** Opens the proof obligation of the failure with the given index and makes it the current one. */
  def openObligation(idx: Int): DebugCommandResult = guarded { msgs =>
    if (idx < 0 || idx >= allFailures.size) {
      DebugCommandResult.error(s"There is no verification failure with index $idx.")
    } else {
      val currResult = allFailures(idx)
      debugContextOf(currResult) match {
        case None =>
          DebugCommandResult.error("Debugging results are not available. No failure context found.")
        case Some(ctx) if ctx.state.isEmpty || ctx.verifier.isEmpty =>
          DebugCommandResult.error("State or verifier not found.")
        case Some(ctx) =>
          val newObl = ProofObligation(ctx.state.get, ctx.verifier.get, ctx.proverDecls, ctx.preambleAssumptions,
            ctx.branchConditions, ctx.branchConditionExps, ctx.assumptions, ctx.failedAssertion,
            ctx.failedAssertionExp, None, new DebugExpPrintConfiguration, currResult.message.reason,
            newDebugResolver(), newDebugTranslator())
          currentIndex = Some(idx)
          // The verification already computed a counterexample for this failure; show it right away.
          counterexample = ctx.counterExample.map(CounterexampleModelBuilder.build(_))
          if (counterexample.isEmpty && !counterexamplesAvailable) {
            msgs += DebugMessage.info(
              "No counterexample is available; run the verification with --counterexample=mapped to get one.")
          }
          initTypechecker(newObl, newObl.eAssertion.finalExp, msgs)
          lastSolverOptions = config.proverArgs
          val initialized = initVerifier(newObl, Z3ProverStdIO.name, lastSolverOptions, msgs)
          obl = Some(initialized)
          originalObl = Some(initialized)
          result(msgs)
      }
    }
  }

  /**
    * Makes the state that verifier `v` is in before executing `stmt` the current proof obligation; used when the
    * verification is paused at a breakpoint (see [[DebugRunController]]).
    *
    * This has to be called on the thread of `v` while it is paused, since the path conditions are read from its
    * decider. Like for a failure, the obligation gets a prover of its own, so the paused verification is not
    * affected by anything the user does with it. There is no assertion to prove, though: the user checks
    * expressions with [[assertText]] instead.
    */
  def openPausedState(s: State, v: Verifier, stmt: ast.Stmt): DebugCommandResult = guarded { msgs =>
    val pcs = v.decider.pcs
    val newObl = ProofObligation(s, v, v.decider.prover.getAllEmits(), v.decider.prover.preambleAssumptions,
      pcs.branchConditions, pcs.branchConditionExps.map(bce => bce._1 -> bce._2.get), pcs.assumptionExps,
      True, DebugExp.createInstance(SiliconDebugSession.noAssertionDescription), None, new DebugExpPrintConfiguration,
      PausedAtStatement(stmt), newDebugResolver(), newDebugTranslator())
    currentIndex = None
    counterexample = None
    initTypechecker(newObl, Some(stmt), msgs)
    lastSolverOptions = config.proverArgs
    val initialized = initVerifier(newObl, Z3ProverStdIO.name, lastSolverOptions, msgs)
    obl = Some(initialized)
    originalObl = Some(initialized)
    result(msgs)
  }

  /** Whether the current obligation is a paused verification rather than a failure; see [[openPausedState]]. */
  def isPaused: Boolean = obl.exists(_.originalErrorReason.isInstanceOf[PausedAtStatement])

  /**
    * Folds (`unfold = false`) or unfolds the predicate instance `text`, e.g. `list(x)` or `acc(list(x), 1/2)`, in the
    * current state, as if the statement `fold`/`unfold` was executed there. This is done on the obligation's own
    * prover, so the verification is not affected.
    *
    * Unfolding a predicate with a conditional body may produce several cases, one for each feasible branch of the
    * body; the first one becomes the current obligation and [[selectCase]] switches to the others. A failed fold
    * (or unfold) leaves the obligation unchanged and reports why it failed.
    *
    * Since the heap changes, the failed assertion the obligation was opened for may no longer describe the failed
    * check; [[recheck]] checks it again in the current state.
    */
  def foldText(text: String, unfold: Boolean): DebugCommandResult = withObligation { (o, msgs) =>
    // Typechecked like the argument of a fold or unfold statement, rather than as an assertion.
    translateStringToExp(text, o, predicateAccess = Some(if (unfold) "unfolded" else "folded")) match {
      case pap: ast.PredicateAccessPredicate => execPredicateStatement(pap, unfold, o, msgs)
      case pa: ast.PredicateAccess => execPredicateStatement(ast.PredicateAccessPredicate(pa, None)(pa.pos), unfold, o, msgs)
      case other => DebugCommandResult.error(s"`$other` is not a predicate instance such as list(x).")
    }
  }

  private def execPredicateStatement(pap: ast.PredicateAccessPredicate, unfold: Boolean, o: ProofObligation,
                                     msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult = {
    // The user's input is typechecked against the whole program, but the verified one may only have been part of it,
    // in which predicates whose bodies its members do not need are abstract (see Silver's chopper).
    val name = pap.loc.predicateName
    if (o.s.program.predicates.find(_.name == name).forall(_.body.isEmpty)) {
      return DebugCommandResult.error(s"The predicate $name has no body in the program that was verified, which " +
        "was probably restricted to the member that failed. Debug the whole file to fold or unfold it (in the Viper " +
        "IDE: disable the setting viper.debugger.restrictToFailingMember, or start the debugger with F5).")
    }
    val stmt = if (unfold) ast.Unfold(pap)(pap.pos) else ast.Fold(pap)(pap.pos)
    val v = o.v
    val emitsBefore = v.decider.prover.getAllEmits().size
    val mark = v.decider.setPathConditionMark()
    val outcomes = mutable.ListBuffer.empty[(State, RecordedPathConditions)]
    // exec2 rather than exec, which would also call the debug hook.
    val res = executor.exec2(o.s, stmt, v)((s1, v1) => {
      // The path conditions of each case are popped again once the case is done, so they are recorded here.
      outcomes += ((s1, v1.decider.pcs.after(mark)))
      Success()
    })
    // Everything the fold or unfold declared, e.g. the snapshots of the new chunks.
    val newEmits = v.decider.prover.getAllEmits().drop(emitsBefore)

    res match {
      case f: Failure =>
        msgs += DebugMessage.error(s"${if (unfold) "Unfolding" else "Folding"} ${pap.loc} failed: ${f.message.reason.readableMessage}")
        // The attempt may have left assumptions in the prover; start from the obligation again.
        obl = Some(initVerifier(o, v.decider.prover.name, lastSolverOptions, msgs))
        result(msgs, ok = false)
      case _ if outcomes.isEmpty =>
        msgs += DebugMessage.warning(
          s"No case of ${pap.loc} is feasible: the assumptions are contradictory after this statement.")
        obl = Some(initVerifier(o, v.decider.prover.name, lastSolverOptions, msgs))
        result(msgs)
      case _ =>
        val newCases = outcomes.toSeq.map { case (s1, pcs) =>
          val conditions = pcs.branchConditionExps.toSeq.map(bce => bce._1 -> bce._2.getOrElse(bce._1))
          val description = conditions.map(_._2.toString).filterNot(_ == "true").mkString(" && ")
          (if (description.isEmpty) "no conditions" else description) -> o.copy(
            s = s1,
            proverEmits = o.proverEmits ++ newEmits,
            branchConditions = o.branchConditions ++ pcs.branchConditions.toSeq,
            branchConditionExps = o.branchConditionExps ++ conditions,
            assumptionsExp = o.assumptionsExp ++ pcs.assumptionExps,
            assertionOutdated = o.assertionOutdated || !isPaused)
        }
        cases = newCases
        invalidateCounterexample()
        msgs += DebugMessage.info(s"${if (unfold) "Unfolded" else "Folded"} ${pap.loc}.")
        if (newCases.size > 1) {
          msgs += DebugMessage.info(s"This produced ${newCases.size} cases; showing case 1. Use :case <n> to switch:\n" +
            newCases.zipWithIndex.map { case ((d, _), i) => s"  [${i + 1}] $d" }.mkString("\n"))
        }
        obl = Some(initVerifier(newCases.head._2, v.decider.prover.name, lastSolverOptions, msgs))
        result(msgs)
    }
  }

  /** Makes case `n` (1-based) of the last fold or unfold the current obligation; see [[foldText]]. */
  def selectCase(n: Int): DebugCommandResult = withObligation { (o, msgs) =>
    if (n < 1 || n > cases.size) {
      DebugCommandResult.error(
        if (cases.isEmpty) "The last fold or unfold did not produce several cases."
        else s"There are only ${cases.size} cases.")
    } else {
      msgs += DebugMessage.info(s"Showing case $n: ${cases(n - 1)._1}. Changes to the previous case were discarded.")
      invalidateCounterexample()
      obl = Some(initVerifier(cases(n - 1)._2, o.v.decider.prover.name, lastSolverOptions, msgs))
      result(msgs)
    }
  }

  /**
    * Checks the assertion that failed again, in the current state: the expression is evaluated (for a location that
    * could not be accessed) or consumed (for an assertion that might not hold) on the obligation's own prover, like
    * the verification does. This is useful after a fold or unfold, which changes the state but not the failed
    * check the obligation was opened for (see [[ProofObligation.assertionOutdated]]).
    *
    * The check is best effort: it is the node the verification error points to that is checked, which may be part
    * of a larger assertion.
    */
  def recheck(): DebugCommandResult = withObligation { (o, msgs) =>
    if (isPaused) {
      DebugCommandResult.error(SiliconDebugSession.noAssertionDescription)
    } else {
      val checked: Either[String, VerificationResult] = o.originalErrorReason.offendingNode match {
        case loc: ast.LocationAccess =>
          val pve = PartialVerificationError(r => ContractNotWellformed(loc, r))
          Right(evaluator.eval3(o.s, loc, pve, o.v)((_, _, _, _) => Success()))
        case e: ast.Exp =>
          val pve = PartialVerificationError(r => AssertFailed(ast.Assert(e)(e.pos), r))
          Right(consumer.consume(o.s, e, returnSnap = false, pve, o.v)((_, _, _) => Success()))
        case other =>
          Left(s"The failure points to `$other`, which cannot be checked again.")
      }
      checked match {
        case Left(err) => DebugCommandResult.error(err)
        case Right(res) =>
          val passed = !res.isInstanceOf[Failure]
          val what = o.originalErrorReason.offendingNode
          res match {
            case f: Failure =>
              msgs += DebugMessage.info(s"FAIL: `$what` still fails: ${f.message.reason.readableMessage}\n")
            case _ =>
              msgs += DebugMessage.info(s"PASS: `$what` holds in this state.\n")
          }
          // The check may have left assumptions in the prover; start from the obligation again.
          obl = Some(initVerifier(o, o.v.decider.prover.name, lastSolverOptions, msgs))
          result(msgs).copy(proved = Some(passed))
      }
    }
  }

  /** Discards all changes made to the current obligation. */
  def reset(): DebugCommandResult = withObligation { (_, msgs) =>
    cases = Seq.empty
    lastSolverOptions = None
    invalidateCounterexample()
    val base = originalObl.get
    obl = Some(initVerifier(base, base.v.decider.prover.name, lastSolverOptions, msgs))
    result(msgs)
  }

  /** The children of the node with the given id; the counterpart of the CLI's "zoom" command. */
  def expand(nodeId: Int): Either[String, Seq[DebugNode]] = {
    obl match {
      case None => Left("There is no proof obligation to inspect.")
      case Some(o) =>
        val filter = DebugNodeFilter.fromPrintConfig(o.printConfig)
        val found = o.assumptionsExp.toSeq.view
          .map(_.getExpWithId(nodeId, new mutable.HashSet()))
          .collectFirst { case Some(de) => de }
        found match {
          case None => Left("Assumption not found")
          case Some(de) =>
            Right(de.children.toSeq
              .filter(d => !d.isInternal || filter.includeInternal)
              .flatMap(_.toNode(filter)))
        }
    }
  }

  def removeAssumptions(ids: Seq[Int]): DebugCommandResult = withObligation { (o, msgs) =>
    msgs += DebugMessage.info(s"Removing assumptions with IDs ${ids.mkString(",")}")
    invalidateCounterexample()
    obl = Some(initVerifier(o.removeAssumptions(ids), o.v.decider.prover.name, lastSolverOptions, msgs))
    result(msgs)
  }

  /**
    * Evaluates the given expression in the current state and adds it to the assumptions. If `free` is false,
    * the expression must be provable from the current assumptions, otherwise it is not added.
    */
  def addAssumption(text: String, free: Boolean): DebugCommandResult = withObligation { (o, msgs) =>
    addAssumption(translateStringToExp(text, o), free, o, msgs)
  }

  /**
    * Like [[addAssumption]], but for an expression that has already been translated to Viper.
    *
    * A frontend whose programs are not parsed from Viper source has no parser state the debugger could use, so it
    * cannot let the user type Viper text; instead it translates the user's input in its own source language itself
    * and passes the result here.
    */
  def addAssumptionExp(e: ast.Exp, free: Boolean): DebugCommandResult = withObligation { (o, msgs) =>
    addAssumption(e, free, o, msgs)
  }

  /**
    * Evaluates the given expression in the current state and asks the prover whether it holds, without adding it
    * to the assumptions. Unlike [[addAssumptionExp]] with `free = false`, the obligation is left unchanged even if
    * the expression is proved.
    *
    * Note that evaluating an expression may still assume its well-definedness conditions (that a receiver is
    * non-null, say); use [[reset]] to get rid of those.
    */
  def assertExp(e: ast.Exp): DebugCommandResult = withObligation { (o, msgs) =>
    assertExp(e, o, msgs)
  }

  /** Like [[assertExp]], for an expression entered as Viper source text. */
  def assertText(text: String): DebugCommandResult = withObligation { (o, msgs) =>
    assertExp(translateStringToExp(text, o), o, msgs)
  }

  private def assertExp(e: ast.Exp, o: ProofObligation, msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult = {
    evalExp(e, o, o.v, msgs) match {
      case Some((_, resT, _, resV, _)) =>
        val proved = resV.decider.prover.assert(resT, o.timeout)
        msgs += DebugMessage.info(
          if (proved) "PASS: The expression holds in this state.\n"
          else "FAIL: The expression could not be proved in this state.\n")
        result(msgs).copy(proved = Some(proved))
      case None =>
        result(msgs, ok = false)
    }
  }

  private def addAssumption(assumptionE: ast.Exp, free: Boolean, o: ProofObligation,
                            msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult = {
    evalAssumption(assumptionE, o, free, o.v, msgs) match {
      case Some((resS, resT, resE, evalAssumptions)) =>
        val allAssumptions = o.assumptionsExp ++ evalAssumptions + DebugExp.createInstance(assumptionE, resE).withTerm(resT)
        invalidateCounterexample()
        obl = Some(o.copy(s = resS, assumptionsExp = allAssumptions))
        result(msgs)
      case None =>
        result(msgs, ok = false)
    }
  }

  /**
    * Asks the prover whether the proof obligation holds.
    *
    * If it does not, the prover has just produced a model of the assumptions and the negated assertion; that
    * model is turned into a counterexample of the state as it is now, including any assumptions the user has
    * added or removed. If the obligation holds, there can be no counterexample and the previous one is dropped.
    */
  def prove(): DebugCommandResult =
    if (isPaused) DebugCommandResult.error(SiliconDebugSession.noAssertionDescription)
    else withObligation { (o, msgs) =>
      val proved = o.v.decider.prover.assert(o.assertion, o.timeout)
      if (proved) {
        msgs += DebugMessage.info("PASS: Proving obligation was successful.\n")
        counterexample = None
      } else {
        msgs += DebugMessage.info("FAIL: Proving obligation failed.\n")
        updateCounterexampleFromProver(o, msgs)
      }
      result(msgs).copy(proved = Some(proved))
    }

  /**
    * Extracts a counterexample from the model the prover produced for the last failed proof attempt.
    *
    * The model describes the state the obligation is about, so it is interpreted against the symbolic state of
    * the obligation, exactly like the counterexample Silicon reports for a verification error.
    */
  private def updateCounterexampleFromProver(o: ProofObligation, msgs: mutable.ListBuffer[DebugMessage]): Unit = {
    if (!counterexamplesAvailable) {
      invalidateCounterexample()
      msgs += DebugMessage.info(
        "No counterexample was computed; run the verification with --counterexample=mapped to get one.")
      return
    }
    val decider = o.v.decider
    if (!decider.hasModel()) decider.generateModel()
    if (!decider.isModelValid()) {
      invalidateCounterexample()
      msgs += DebugMessage.warning("The prover did not provide a model for this proof obligation.")
      return
    }
    try {
      val ce = SiliconMappedCounterexample(o.s.g, o.s.h.values, o.s.oldHeaps, decider.getModel(), o.s.program)
      counterexample = Some(CounterexampleModelBuilder.build(ce))
    } catch {
      case e: Throwable =>
        invalidateCounterexample()
        msgs += DebugMessage.warning(s"The counterexample could not be built: ${e.getMessage}")
    }
  }

  def setTimeout(ms: Option[Int]): DebugCommandResult = withObligation { (o, msgs) =>
    obl = Some(o.copy(timeout = ms.filter(_ > 0)))
    result(msgs)
  }

  def setProver(name: String, args: Option[String]): DebugCommandResult = withObligation { (o, msgs) =>
    if (!SiliconDebugSession.proverNames.contains(name)) {
      DebugCommandResult.error(s"Invalid prover name '$name'. Options are ${SiliconDebugSession.proverNames.mkString(", ")}.")
    } else {
      lastSolverOptions = args.filter(_.nonEmpty)
      obl = Some(initVerifier(o, name, lastSolverOptions, msgs))
      result(msgs)
    }
  }

  def setPrintConfig(c: PrintConfigModel): DebugCommandResult = withObligation { (o, msgs) =>
    o.printConfig.applyModel(c)
    result(msgs)
  }

  /** Stops the prover started for this session and releases the symbolic state it kept alive. */
  def close(): Unit = {
    closed = true
    stopCurrentWorker()
    obl = None
    originalObl = None
    counterexample = None
  }

  // -------------------------------------------------------------------------------------------------------
  // Internals
  // -------------------------------------------------------------------------------------------------------

  private def result(msgs: mutable.ListBuffer[DebugMessage], ok: Boolean = true): DebugCommandResult =
    DebugCommandResult(ok, msgs.toSeq, obl.map(buildModel))

  /** Runs a command, turning any exception into an error result so that clients never see one. */
  private def guarded(f: mutable.ListBuffer[DebugMessage] => DebugCommandResult): DebugCommandResult = {
    if (closed) return DebugCommandResult.error("This debug session has been closed.")
    val msgs = mutable.ListBuffer.empty[DebugMessage]
    try f(msgs)
    catch {
      case e: Throwable =>
        DebugCommandResult(ok = false, msgs.toSeq :+ DebugMessage.error(s"Unexpected error: ${e.getMessage}"),
          obl.map(buildModel))
    }
  }

  private def withObligation(f: (ProofObligation, mutable.ListBuffer[DebugMessage]) => DebugCommandResult): DebugCommandResult =
    guarded { msgs =>
      obl match {
        case Some(o) => f(o, msgs)
        case None => DebugCommandResult.error("There is no proof obligation to debug.")
      }
    }

  private def stopCurrentWorker(): Unit = {
    currentWorker.foreach(w => try w.stop() catch { case _: Throwable => })
    currentWorker = None
  }

  private def newDebugResolver(): Option[DebugResolver] =
    for (r <- resolver; pp <- pprogram) yield new DebugResolver(pp, r.names)

  private def newDebugTranslator(): Option[DebugTranslator] =
    for (t <- translator; pp <- pprogram) yield new DebugTranslator(pp, t.getMembers())

  /** Sets up the typechecker for user input in the scope of `node`, i.e. of the member that contains it. */
  private def initTypechecker(obl: ProofObligation, node: Option[ast.Infoed],
                              msgs: mutable.ListBuffer[DebugMessage]): Unit = {
    // Without a resolver there is nothing to typecheck against; the user cannot enter expressions as text in that
    // case anyway (see `acceptsTextualExpressions`), so this is not worth a warning.
    val resolver = obl.resolver.getOrElse(return)
    def sourceOf(n: ast.Infoed): Option[PNode] = n.info.getUniqueInfo[SourcePNodeInfo].map(_.sourcePNode)
    // A failure that is not about an assertion that might not hold (e.g. missing permission) has no expression for the
    // failed assertion; the node the error points to, or else the member being verified, gives the scope then.
    val offendingNode = Some(obl.originalErrorReason.offendingNode).collect { case n: ast.Infoed => n }
    var failedPExp: Option[PNode] =
      node.flatMap(sourceOf)
        .orElse(offendingNode.flatMap(sourceOf))
        .orElse(obl.s.currentMember.flatMap(sourceOf))
    while (failedPExp.isDefined && !failedPExp.get.isInstanceOf[PScope]) {
      failedPExp = failedPExp.get.getParent
    }
    if (failedPExp.isDefined) {
      resolver.typechecker.curMember = failedPExp.get.asInstanceOf[PScope]
    } else {
      msgs += DebugMessage.warning("Could not determine the scope for typechecking.")
    }

    resolver.typechecker.debugVariableTypes =
      obl.v.decider.debugVariableTypes map { case (str, pType) => (simplifyVariableName(str), pType) }
  }

  /**
    * Creates a fresh verifier with its own prover for the given obligation and replays the declarations and
    * assumptions of the failed verification into it.
    */
  private def initVerifier(obl: ProofObligation, proverName: String, userArgsString: Option[String],
                           msgs: mutable.ListBuffer[DebugMessage]): ProofObligation = {
    // Stop the prover of the previous obligation; otherwise every command would leak a prover process.
    stopCurrentWorker()

    val v = new WorkerVerifier(this.mainVerifier, obl.v.uniqueId, NoopReporter, false)
    v.debugHookEnabled = false
    currentWorker = Some(v)
    v.start()
    v.decider.createProver(proverName, userArgsString)
    v.decider.prover.emit(obl.proverEmits)

    obl.preambleAssumptions foreach (a => v.decider.prover.assumeAxioms(a.terms, a.description))

    msgs += DebugMessage.info("Initializing prover...")
    obl.assumptionsExp foreach (debugExp => v.decider.debuggerAssume(debugExp.getAllTerms(new mutable.HashSet()), debugExp))
    obl.copy(v = v)
  }

  /**
    * Parses, typechecks and translates an expression entered by the user.
    *
    * @param predicateAccess if given, the expression has to be a predicate access, like the argument of a fold or
    *                        unfold statement (the value says which, for the message about abstract predicates);
    *                        otherwise, it has to be a boolean expression.
    */
  private def translateStringToExp(str: String, obl: ProofObligation, predicateAccess: Option[String] = None): ast.Exp = {
    val resolver = obl.resolver.getOrElse(throw new RuntimeException(
      "This program was not parsed from Viper source, so expressions cannot be entered as Viper text. " +
        "The frontend has to translate the expression itself and use addAssumptionExp/assertExp."))
    val translator = obl.translator.getOrElse(throw new RuntimeException(
      "This program was not parsed from Viper source, so expressions cannot be entered as Viper text. " +
        "The frontend has to translate the expression itself and use addAssumptionExp/assertExp."))

    def parseToPExp(): PExp = {
      try {
        debugParser._line_offset = Seq(0, str.length + 1).toArray
        debugParser._file = Paths.get("userInput")
        val parsedExp = fastparse.parse(str, debugParser.exp(_))
        parsedExp.get.value
      } catch {
        case e: Throwable => throw new RuntimeException(s"Error while parsing $str: ${e.getMessage}", e)
      }
    }

    def typecheckPExp(pexp: PExp): Unit = {
      try {
        resolver.typechecker.names.check(pexp, None, resolver.typechecker.curMember)
        predicateAccess match {
          case Some(how) =>
            resolver.typechecker.acceptNonAbstractPredicateAccess(pexp, s"abstract predicates cannot be $how")
            resolver.typechecker.check(pexp, TypeHelper.Predicate)
          case None =>
            resolver.typechecker.check(pexp, PPrimitiv(PReserved(PKw.Bool)((NoPosition, NoPosition)))())
        }
      } catch {
        case e: Throwable => throw new RuntimeException(s"Error while typechecking $str: ${e.getMessage}", e)
      }
      if (resolver.messages.nonEmpty) {
        val msg = resolver.messages.mkString("\n\t")
        resolver.names.messages = Seq()
        resolver.typechecker.messages = Seq()
        throw new RuntimeException(s"Error while typechecking:\n\t $msg")
      }
    }

    def translatePExp(pexp: PExp): ast.Exp = {
      try {
        translator.exp(pexp)
      } catch {
        case e: Throwable => throw new RuntimeException(s"Error while translating $str: ${e.getMessage}", e)
      }
    }

    val pexp = parseToPExp()
    typecheckPExp(pexp)
    translatePExp(pexp)
  }

  /**
    * Symbolically evaluates the given expression in the state of the obligation, and returns the resulting state,
    * term and expression together with the assumptions the evaluation itself produced.
    */
  private def evalExp(e: ast.Exp, obl: ProofObligation, v: Verifier, msgs: mutable.ListBuffer[DebugMessage])
                     : Option[(State, Term, ast.Exp, Verifier, InsertionOrderedSet[DebugExp])] = {
    var resT: Term = null
    var resS: State = null
    var resE: ast.Exp = null
    var resV: Verifier = null
    var evalPcs: RecordedPathConditions = null
    val pve: PartialVerificationError = PartialVerificationError(r => ContractNotWellformed(e, r))
    val beforeEval = v.decider.setPathConditionMark()
    val verificationResult = evaluator.eval3(obl.s, e, pve, v)((newS, t, newE, newV) => {
      resS = newS
      resT = t
      resE = newE.get
      resV = newV
      evalPcs = newV.decider.pcs.after(beforeEval)
      Success()
    })

    verificationResult match {
      case Success() =>
        Some((resS, resT, resE, resV, evalPcs.assumptionExps))
      case _ =>
        msgs += DebugMessage.error("Error while evaluating expression: " + verificationResult.toString)
        None
    }
  }

  private def evalAssumption(e: ast.Exp, obl: ProofObligation, isFree: Boolean, v: Verifier,
                             msgs: mutable.ListBuffer[DebugMessage]): Option[(State, Term, ast.Exp, InsertionOrderedSet[DebugExp])] = {
    evalExp(e, obl, v, msgs) flatMap { case (resS, resT, resE, resV, evalAssumptions) =>
      val proved = isFree || resV.decider.prover.assert(resT, None)
      if (proved) {
        msgs += DebugMessage.info("Assumption was added successfully!")
        resV.asInstanceOf[WorkerVerifier].decider.debuggerAssume(Seq(resT), null)
        Some((resS, resT, resE, evalAssumptions))
      } else {
        msgs += DebugMessage.error("Fail! Could not prove assumption. Skipping")
        None
      }
    }
  }
}

object SiliconDebugSession {
  val proverNames: Seq[String] = Seq(Z3ProverStdIO.name, Cvc5ProverStdIO.name)

  val noAssertionDescription: String =
    "There is no assertion to prove at a breakpoint; use :assert <expression> to check whether an expression holds."
}
