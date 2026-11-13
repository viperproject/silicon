// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.Config
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.{Cvc5ProverStdIO, RecordedPathConditions, Z3ProverStdIO}
import viper.silicon.interfaces.{Failure, SiliconDebuggingFailureContext, SiliconFailureContext, SiliconMappedCounterexample, Success, VerificationResult}
import viper.silicon.rules.{consumer, evaluator, executor}
import viper.silicon.state.{Identifier, State}
import viper.silicon.state.terms.{ConstDecl, Exists, Forall, Term, True, Var}
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

  /** How many witnesses [[obtainWitness]] has declared, which makes their names unique. */
  private var witnessCount: Int = 0

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
  def openPausedState(s: State, v: Verifier, stmt: ast.Stmt): DebugCommandResult =
    openPaused(s, v, PausedAtStatement(stmt), stmt,
      DebugExp.createInstance(SiliconDebugSession.noAssertionDescription))

  /**
    * Like [[openPausedState]], but for a verification that is paused before checking `assertion`, a conjunct of the
    * specification that `description` names. The assertion to prove is `assertion`, in the scope of the
    * specification: at a call, the store maps the parameters of the called method. [[prove]] checks it the way the
    * verification is about to.
    */
  def openPausedCheck(s: State, v: Verifier, assertion: ast.Exp, description: String): DebugCommandResult =
    openPaused(s, v, PausedAtCheck(assertion, description), assertion, DebugExp.createInstance(assertion, assertion))

  private def openPaused(s: State, v: Verifier, reason: PausedReason, scope: ast.Infoed,
                         eAssertion: DebugExp): DebugCommandResult = guarded { msgs =>
    val pcs = v.decider.pcs
    val newObl = ProofObligation(s, v, v.decider.prover.getAllEmits(), v.decider.prover.preambleAssumptions,
      pcs.branchConditions, pcs.branchConditionExps.map(bce => bce._1 -> bce._2.get), pcs.assumptionExps,
      True, eAssertion, None, new DebugExpPrintConfiguration, reason, newDebugResolver(), newDebugTranslator())
    currentIndex = None
    counterexample = None
    initTypechecker(newObl, Some(scope), msgs)
    lastSolverOptions = config.proverArgs
    val initialized = initVerifier(newObl, Z3ProverStdIO.name, lastSolverOptions, msgs)
    obl = Some(initialized)
    originalObl = Some(initialized)
    result(msgs)
  }

  /**
    * Whether the current obligation is a paused verification rather than a failure; see [[openPausedState]] and
    * [[openPausedCheck]].
    */
  def isPaused: Boolean = obl.exists(_.originalErrorReason.isInstanceOf[PausedReason])

  /** Whether the current obligation is a verification paused before a statement, so there is nothing to prove. */
  private def isPausedAtStatement: Boolean = obl.exists(_.originalErrorReason.isInstanceOf[PausedAtStatement])

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
    * check; [[prove]] checks it again in the current state.
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
    val command = s"${if (unfold) "unfold" else "fold"} ${if (pap.perm.isInstanceOf[ast.FullPerm]) pap.loc else pap}"
    execStatement(stmt, command, o, msgs)(
      failed = reason => s"${if (unfold) "Unfolding" else "Folding"} ${pap.loc} failed: $reason",
      succeeded = s"${if (unfold) "Unfolded" else "Folded"} ${pap.loc}.",
      infeasible = s"No case of ${pap.loc} is feasible: the assumptions are contradictory after this statement.")
  }

  /**
    * Adds an impure assertion such as `acc(x.f) && x.f > 0` to the state: if `free`, as if `inhale e` was executed,
    * which adds its permissions to the heap and its pure parts to the assumptions; otherwise as if `assert e` was
    * executed, which checks that the state has the permissions and that the pure parts hold, and then adds the pure
    * parts. Like an unfold, a conditional assertion may produce several cases.
    */
  private def addImpureAssumption(e: ast.Exp, free: Boolean, o: ProofObligation,
                                  msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult = {
    val stmt = if (free) ast.Inhale(e)(e.pos) else ast.Assert(e)(e.pos)
    execStatement(stmt, s"${if (free) "assume" else "assert"} $e", o, msgs)(
      failed = reason => s"Fail! Could not prove $e: $reason",
      succeeded = if (free) s"Added $e to the state." else s"Proved $e and added it to the assumptions.",
      infeasible = s"The state is infeasible after adding $e, e.g. because it adds more permission than the state " +
        "can hold. The assumption was not added.")
  }

  /**
    * Executes `stmt` in the current state, as if it occurred there in the program, and records what it changed as done
    * by the debugger command `command`. This is done on the obligation's own prover, so the verification is not
    * affected. Each feasible outcome becomes a case (see [[selectCase]]), the first of which becomes the current
    * obligation; if the statement fails, the obligation is left unchanged.
    *
    * Since the heap may change, the failed assertion the obligation was opened for may no longer describe the failed
    * check; [[prove]] checks it again in the current state.
    */
  private def execStatement(stmt: ast.Stmt, command: String, o: ProofObligation, msgs: mutable.ListBuffer[DebugMessage])
                           (failed: String => String, succeeded: String, infeasible: String): DebugCommandResult = {
    val v = o.v
    val emitsBefore = v.decider.prover.getAllEmits().size
    val mark = v.decider.setPathConditionMark()
    val outcomes = mutable.ListBuffer.empty[(State, RecordedPathConditions)]
    // exec2 rather than exec, which would also call the debug hook.
    val res = executor.exec2(o.s, stmt, v)((s1, v1) => {
      // The path conditions of each case are popped again once the case is done, so they are recorded here. An
      // outcome whose path conditions are contradictory, e.g. after adding permission the state already has, is
      // dropped.
      if (!v1.decider.checkSmoke()) outcomes += ((s1, v1.decider.pcs.after(mark)))
      Success()
    })
    // Everything the statement declared, e.g. the snapshots of new chunks.
    val newEmits = v.decider.prover.getAllEmits().drop(emitsBefore)

    res match {
      case f: Failure =>
        msgs += DebugMessage.error(failed(f.message.reason.readableMessage))
        // The attempt may have left assumptions in the prover; start from the obligation again.
        obl = Some(initVerifier(o, v.decider.prover.name, lastSolverOptions, msgs))
        result(msgs, ok = false)
      case _ if outcomes.isEmpty =>
        msgs += DebugMessage.warning(infeasible)
        obl = Some(initVerifier(o, v.decider.prover.name, lastSolverOptions, msgs))
        result(msgs)
      case _ =>
        val newCases = outcomes.toSeq.map { case (s1, pcs) =>
          val conditions = pcs.branchConditionExps.toSeq.map(bce => bce._1 -> bce._2.getOrElse(bce._1))
          val description = conditions.map(_._2.toString).filterNot(_ == "true").mkString(" && ")
          (if (description.isEmpty) "no conditions" else description) -> o.changedBy(command, o.copy(
            s = s1,
            proverEmits = o.proverEmits ++ newEmits,
            branchConditions = o.branchConditions ++ pcs.branchConditions.toSeq,
            branchConditionExps = o.branchConditionExps ++ conditions,
            assumptionsExp = o.assumptionsExp ++ pcs.assumptionExps,
            assertionOutdated = o.assertionOutdated || (!isPaused && s1.h.values != o.s.h.values)))
        }
        cases = newCases
        invalidateCounterexample()
        msgs += DebugMessage.info(succeeded)
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
        // Removed assumptions are still shown, see UserChanges.removedAssumptions.
        val found = (o.assumptionsExp.toSeq ++ o.userChanges.removedAssumptions.map(_._1)).view
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

  def removeAssumptions(ids: Seq[Int]): DebugCommandResult = remove(ids, Seq.empty)

  /**
    * Removes the assumptions with ids `assumptionIds` and the chunks `hn` of the current heap with the numbers `n` in
    * `chunkNumbers`, see [[ProofObligation.removeChunks]]. Use [[parseRemovalTargets]] to read both from text such as
    * `12, h3`.
    */
  def remove(assumptionIds: Seq[Int], chunkNumbers: Seq[Int]): DebugCommandResult = withObligation { (o, msgs) =>
    val count = o.s.h.values.size
    val unknown = chunkNumbers.filter(n => n < 1 || n > count)
    if (unknown.nonEmpty) {
      DebugCommandResult.error(s"There is no heap chunk ${unknown.map(n => s"h$n").mkString(", ")}; " +
        (if (count == 0) "the heap is empty." else if (count == 1) "the heap has only h1." else s"the heap has h1 to h$count."))
    } else {
      if (assumptionIds.nonEmpty || chunkNumbers.isEmpty)
        msgs += DebugMessage.info(s"Removing assumptions with IDs ${assumptionIds.mkString(",")}")
      if (chunkNumbers.nonEmpty)
        msgs += DebugMessage.info(s"Removing heap chunks ${chunkNumbers.map(n => s"h$n").mkString(",")}")
      invalidateCounterexample()
      // Like after a fold or unfold, the assertion was evaluated in a heap that has changed.
      val withoutChunks =
        if (chunkNumbers.isEmpty) o
        else o.removeChunks(chunkNumbers).copy(assertionOutdated = o.assertionOutdated || !isPaused)
      obl = Some(initVerifier(withoutChunks.removeAssumptions(assumptionIds), o.v.decider.prover.name, lastSolverOptions, msgs))
      result(msgs)
    }
  }

  /**
    * Evaluates the given expression in the current state and adds it to the assumptions. If `free` is false,
    * the expression must be provable from the current assumptions, otherwise it is not added.
    *
    * An impure expression, e.g. `acc(x.f) && x.f > 0`, is added like an `inhale` (or checked like an `assert` if `free`
    * is false) instead; see [[addImpureAssumption]]. Its permissions can be removed again with [[remove]].
    */
  def addAssumption(text: String, free: Boolean): DebugCommandResult = withObligation { (o, msgs) =>
    addAssumption(translateStringToExp(text, o, impure = true), free, o, msgs)
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

  /**
    * Instantiates the universally quantified assumption with id `id` and adds the instance to the assumptions. This is
    * what the prover does when a trigger of the quantifier matches; it helps when none does.
    *
    * `arguments` are Viper expressions separated by commas, which are evaluated in the current state and replace the
    * first bound variables of the quantifier; with fewer arguments than bound variables, the instance is still
    * quantified over the remaining ones. The instance follows from the quantifier, so adding it is sound. It is
    * removed together with the quantifier, see [[ProofObligation.removeAssumptions]].
    *
    * The quantifier may be nested in another assumption, e.g. among the path conditions of a join: under an
    * implication, the instance only holds under the implication's condition, too. It cannot be nested in another
    * quantifier, whose variables it may refer to.
    */
  def instantiate(id: Int, arguments: String): DebugCommandResult = withObligation { (o, msgs) =>
    val args = SiliconDebugSession.splitArguments(arguments)
    if (args.isEmpty) DebugCommandResult.error("Give the values to instantiate the quantifier with, e.g. :instantiate 12 3, x.")
    else instantiate(id, args.map(translateStringToExp(_, o, anyType = true)), o, msgs)
  }

  /** Like [[instantiate]], for arguments that have already been translated to Viper; see [[addAssumptionExp]]. */
  def instantiateExps(id: Int, arguments: Seq[ast.Exp]): DebugCommandResult = withObligation { (o, msgs) =>
    instantiate(id, arguments, o, msgs)
  }

  private def instantiate(id: Int, args: Seq[ast.Exp], o: ProofObligation,
                          msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult = {
    QuantifiedAssumption.find(o.assumptionsExp, id) match {
      case Left(error) => DebugCommandResult.error(error)
      case Right(q) if q.quantifier != Forall =>
        DebugCommandResult.error(s"[$id] is not a forall, so it cannot be instantiated with any values; " +
          s"use :witness $id to obtain a witness of it.")
      case Right(forall) if args.isEmpty || args.size > forall.vars.size =>
        DebugCommandResult.error(s"[$id] binds ${forall.vars.size} variable(s), ${forall.varNames.mkString(", ")}; " +
          s"give between 1 and ${forall.vars.size} values, not ${args.size}.")
      case Right(forall) =>
        val v = o.v
        val emitsBefore = v.decider.prover.getAllEmits().size
        val mark = v.decider.setPathConditionMark()
        val outcomes = mutable.ListBuffer.empty[(State, Seq[Term], RecordedPathConditions)]
        val pvef = (e: ast.Exp) => PartialVerificationError(r => ContractNotWellformed(e, r))
        val res = evaluator.evals(o.s, args, pvef, v)((s1, ts, _, v1) => {
          outcomes += ((s1, ts, v1.decider.pcs.after(mark)))
          Success()
        })
        val newEmits = v.decider.prover.getAllEmits().drop(emitsBefore)
        val mismatch = outcomes.headOption.flatMap { case (_, ts, _) =>
          forall.varNames.zip(forall.vars).zip(args.zip(ts)).collectFirst {
            case ((name, x), (e, t)) if t.sort != x.sort => s"`$e` is of sort ${t.sort}, but $name is of sort ${x.sort}."
          }
        }
        val failure = res match {
          case f: Failure => Some(s"Evaluating the values failed: ${f.message.reason.readableMessage}")
          case _ if outcomes.isEmpty => Some("Evaluating the values is not feasible: the assumptions are contradictory.")
          case _ if outcomes.size > 1 || outcomes.head._3.branchConditions.nonEmpty =>
            Some("Evaluating the values branches, e.g. on a conditional expression; give values that do not.")
          case _ => mismatch
        }
        failure match {
          case Some(message) =>
            msgs += DebugMessage.error(message)
            // The evaluation may have left assumptions in the prover; start from the obligation again.
            obl = Some(initVerifier(o, v.decider.prover.name, lastSolverOptions, msgs))
            result(msgs, ok = false)
          case None =>
            val (s1, ts, pcs) = outcomes.head
            val bindings = forall.varNames.zip(args).map { case (x, e) => s"$x := $e" }.mkString(", ")
            val instance = DebugExp.createInstantiationInstance(id, s"instance of [$id] with $bindings",
              forall.instantiateExp(args), forall.instantiate(ts))
            v.asInstanceOf[WorkerVerifier].decider.debuggerAssume(instance.term.toSeq, instance)
            invalidateCounterexample()
            obl = Some(o.changedBy(s"instantiate [$id] with $bindings", o.copy(s = s1,
              proverEmits = o.proverEmits ++ newEmits, assumptionsExp = o.assumptionsExp ++ pcs.assumptionExps + instance)))
            msgs += DebugMessage.info(s"Added [${instance.id}], the instance of [$id] with $bindings.")
            result(msgs)
        }
    }
  }

  /**
    * Obtains a witness of the existentially quantified assumption with id `id`: declares a fresh constant for each of
    * its bound variables and assumes the body for these constants. This is sound, since nothing else is known about
    * the constants, and lets the user refer to the value whose existence the assumption states, e.g. to instantiate a
    * forall with it.
    *
    * The constants are added to the store, named after the bound variables, e.g. `i_witness@1` for `i`; that is
    * also how the user refers to them in expressions. Like an instance (see [[instantiate]]), the witness is removed
    * together with the quantifier, and the quantifier may be nested in an implication, whose condition then guards
    * the witness.
    */
  def obtainWitness(id: Int): DebugCommandResult = withObligation { (o, msgs) =>
    QuantifiedAssumption.find(o.assumptionsExp, id) match {
      case Left(error) => DebugCommandResult.error(error)
      case Right(q) if q.quantifier != Exists =>
        DebugCommandResult.error(s"[$id] is not an exists; use :instantiate $id <values> to instantiate a forall.")
      case Right(exists) =>
        val v = o.v
        val emitsBefore = v.decider.prover.getAllEmits().size
        val witnesses = exists.varNames.zip(exists.vars).map { case (name, x) =>
          witnessCount += 1
          val base = if (name.contains("@")) name.substring(0, name.indexOf("@")) else name
          // The name the user types, which the evaluator turns into this constant, see Evaluator (LocalVarWithVersion).
          val userName = s"${base}_witness@$witnessCount"
          val constant = Var(Identifier(s"$userName@${v.uniqueId}"), x.sort, false)
          v.decider.prover.declare(ConstDecl(constant))
          (userName, constant)
        }
        val newEmits = v.decider.prover.getAllEmits().drop(emitsBefore)
        val eWitnesses = exists.eVars.map(_.zip(witnesses).map { case (d, (n, _)) => ast.LocalVarWithVersion(n, d.typ)() })

        val names = witnesses.map(_._1).mkString(", ")
        val witness = DebugExp.createInstantiationInstance(id, s"witness of [$id]: $names",
          eWitnesses.flatMap(exists.instantiateExp), exists.instantiate(witnesses.map(_._2)))
        v.asInstanceOf[WorkerVerifier].decider.debuggerAssume(witness.term.toSeq, witness)

        // Without the types of the bound variables, the witnesses can only be used by the prover, not in expressions.
        val store = eWitnesses.toSeq.flatMap(_.zip(witnesses)).foldLeft(o.s.g) { case (g, (w, (_, t))) => g + (w -> (t, Some(w))) }
        for (r <- o.resolver; vs <- exists.eVars; (d, (n, _)) <- vs.zip(witnesses)) {
          r.typechecker.debugVariableTypes.get(d.name).foreach(t => r.typechecker.debugVariableTypes += (n -> t))
        }
        invalidateCounterexample()
        obl = Some(o.changedBy(s"witness of [$id]", o.copy(s = o.s.copy(g = store),
          proverEmits = o.proverEmits ++ newEmits, assumptionsExp = o.assumptionsExp + witness)))
        msgs += DebugMessage.info(s"Added [${witness.id}], the witness $names of [$id]: ${witness.finalExp.getOrElse(witness.term.get)}")
        result(msgs)
    }
  }

  private def addAssumption(assumptionE: ast.Exp, free: Boolean, o: ProofObligation,
                            msgs: mutable.ListBuffer[DebugMessage]): DebugCommandResult =
    if (!assumptionE.isPure) addImpureAssumption(assumptionE, free, o, msgs)
    else evalAssumption(assumptionE, o, free, o.v, msgs) match {
      case Some((resS, resT, resE, evalAssumptions)) =>
        val allAssumptions = o.assumptionsExp ++ evalAssumptions + DebugExp.createInstance(assumptionE, resE).withTerm(resT)
        invalidateCounterexample()
        obl = Some(o.changedBy(s"${if (free) "assume" else "assert"} $assumptionE",
          o.copy(s = resS, assumptionsExp = allAssumptions)))
        result(msgs)
      case None =>
        result(msgs, ok = false)
    }

  /**
    * Checks whether the proof obligation holds in its current state.
    *
    * The assertion that failed (the node the error points to) is checked again, the way the verification checks it:
    * a location that could not be accessed is evaluated, an assertion that might not hold is consumed. This accounts
    * for everything that was done to the obligation, including folds and unfolds, which change the heap but not the
    * term of the failed check that the verification recorded. If the check fails, the failure comes with a
    * counterexample of the current state (if counterexamples are enabled); if it succeeds, there can be no
    * counterexample and the previous one is dropped.
    *
    * If the node cannot be checked on its own, e.g. because it refers to variables that are bound in a surrounding
    * quantifier, the recorded term of the failed check is proved instead, and the prover's model of its negation
    * becomes the counterexample.
    *
    * If the verification is paused before checking a specification (see [[openPausedCheck]]), the specification's
    * conjunct is checked, which tells whether the check the verification is about to make succeeds.
    */
  def prove(): DebugCommandResult =
    if (isPausedAtStatement) DebugCommandResult.error(SiliconDebugSession.noAssertionDescription)
    else withObligation { (o, msgs) =>
      checkAgain(o) match {
        case Some(res) =>
          val what = o.originalErrorReason.offendingNode
          val proved = res match {
            case f: Failure =>
              msgs += DebugMessage.info(s"FAIL: `$what` might not hold: ${f.message.reason.readableMessage}\n")
              counterexample = counterexampleOf(f)
              if (counterexample.isEmpty) {
                msgs += DebugMessage.info(
                  if (counterexamplesAvailable) "The prover did not provide a counterexample."
                  else "No counterexample was computed; run the verification with --counterexample=mapped to get one.")
              }
              false
            case _ =>
              msgs += DebugMessage.info(s"PASS: `$what` holds in this state.\n")
              counterexample = None
              true
          }
          // The check may have left assumptions (and a model) in the prover; start from the obligation again.
          obl = Some(initVerifier(o, o.v.decider.prover.name, lastSolverOptions, msgs))
          result(msgs).copy(proved = Some(proved))

        case None if isPaused =>
          // There is no recorded check to fall back to before the specification is checked.
          msgs += DebugMessage.error(s"`${o.originalErrorReason.offendingNode}` cannot be checked on its own here.")
          result(msgs, ok = false)

        case None =>
          val proved = o.v.decider.prover.assert(o.assertion, o.timeout)
          if (proved) {
            msgs += DebugMessage.info("PASS: Proving obligation was successful.\n")
            counterexample = None
          } else {
            msgs += DebugMessage.info("FAIL: Proving obligation failed.\n")
            updateCounterexampleFromProver(o, msgs)
          }
          if (o.assertionOutdated) {
            msgs += DebugMessage.warning("The failed assertion could not be checked again in the current state, so " +
              "the check recorded before the last fold or unfold was proved instead.")
          }
          result(msgs).copy(proved = Some(proved))
      }
    }

  /**
    * Checks the node a failure points to again in the obligation's current state, on its own prover; see [[prove]].
    * None if the node cannot be checked on its own: if it is not an expression, if it refers to variables that are
    * neither in the store nor bound in it, or if checking it fails with an exception.
    */
  private def checkAgain(o: ProofObligation): Option[VerificationResult] = {
    o.originalErrorReason.offendingNode match {
      case e: ast.Exp =>
        val storeVariables = o.s.g.values.keySet.map(_.name)
        val boundVariables = e.deepCollect { case d: ast.LocalVarDecl => d.name }.toSet
        val variables = e.deepCollect { case v: ast.AbstractLocalVar => v.name }
        if (!variables.forall(n => storeVariables.contains(n) || boundVariables.contains(n))) None
        else scala.util.Try(e match {
          case loc: ast.LocationAccess =>
            val pve = PartialVerificationError(r => ContractNotWellformed(loc, r))
            evaluator.eval3(o.s, loc, pve, o.v)((_, _, _, _) => Success())
          case _ =>
            val pve = PartialVerificationError(r => AssertFailed(ast.Assert(e)(e.pos), r))
            consumer.consume(o.s, e, returnSnap = false, pve, o.v)((_, _, _) => Success())
        }).toOption
      case _ => None
    }
  }

  /** The counterexample Silicon attached to a failure, as a model of the debugger. */
  private def counterexampleOf(f: Failure): Option[CounterexampleModel] =
    f.message.failureContexts.collectFirst {
      case c: SiliconDebuggingFailureContext => c.counterExample
      case c: SiliconFailureContext => c.counterExample
    }.flatten.map(CounterexampleModelBuilder.build(_))

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

    // In debug mode, like the verifiers of the verification: only then does the decider record the expressions of
    // what it assumes, which the obligation needs after a command adds assumptions (e.g. an unfold).
    val v = new WorkerVerifier(this.mainVerifier, obl.v.uniqueId, NoopReporter, config.enableDebugging())
    v.debugHookEnabled = false
    currentWorker = Some(v)
    v.start()
    // Fresh identifiers are numbered per verifier id, e.g. $t@12@08, and this verifier has the id of the one that
    // produced the obligation (which names such as x@1 rely on). Continue after every number the replayed declarations
    // use, or a command that declares something (e.g. an inhale) would declare an existing identifier again.
    val numbered = s"@(\\d+)@${java.util.regex.Pattern.quote(v.uniqueId)}(?![0-9])".r
    obl.proverEmits.iterator.flatMap(e => numbered.findAllMatchIn(e).map(_.group(1).toInt)).maxOption
      .foreach(max => v.identifierFactory.skipTo(max + 1))
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
    *                        otherwise, it has to be a boolean expression, unless `anyType`.
    * @param anyType         whether the expression may be of any type, like the value of a variable.
    */
  private def translateStringToExp(str: String, obl: ProofObligation, predicateAccess: Option[String] = None,
                                   anyType: Boolean = false, impure: Boolean = false): ast.Exp = {
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
          case None if anyType =>
            resolver.typechecker.checkTopTyped(pexp, None)
          case None if impure =>
            // Like the assertion of an inhale: Bool, or containing permissions.
            resolver.typechecker.check(pexp, TypeHelper.Impure)
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

  /**
    * The assumption ids and heap chunk numbers in `text`, separated by commas or spaces, e.g. `12, h3` for assumption
    * `[12]` and chunk `[h3]`; see [[SiliconDebugSession.remove]]. Fails with a message naming what is neither.
    */
  def parseRemovalTargets(text: String): Either[String, (Seq[Int], Seq[Int])] = {
    val ChunkHandle = "[hH](\\d+)".r
    val targets = text.split("[,\\s]+").toSeq.filter(_.nonEmpty).map(t => t.stripPrefix("[").stripSuffix("]")).map {
      case ChunkHandle(n) => Right(Right(n.toInt))
      case t => t.toIntOption.map(id => Right(Left(id))).getOrElse(Left(t))
    }
    targets.collect { case Left(t) => t } match {
      case Seq() =>
        val valid = targets.collect { case Right(t) => t }
        Right((valid.collect { case Left(id) => id }, valid.collect { case Right(n) => n }))
      case invalid =>
        Left(s"${invalid.mkString(", ")} ${if (invalid.size == 1) "is" else "are"} neither an assumption id such as 12 " +
          "nor a heap chunk such as h3.")
    }
  }

  /** Splits `text` at the commas that are not nested in parentheses, brackets or braces, e.g. `f(x, y), 3`. */
  def splitArguments(text: String): Seq[String] = {
    val parts = mutable.ListBuffer.empty[String]
    val current = new StringBuilder
    var depth = 0
    text.foreach {
      case ',' if depth == 0 =>
        parts += current.toString
        current.clear()
      case c =>
        if ("([{".contains(c)) depth += 1
        else if (")]}".contains(c)) depth = math.max(0, depth - 1)
        current += c
    }
    parts += current.toString
    parts.toSeq.map(_.trim).filter(_.nonEmpty)
  }

  val noAssertionDescription: String =
    "There is no assertion to prove before a statement; use :assert <expression> to check whether an expression holds."
}
