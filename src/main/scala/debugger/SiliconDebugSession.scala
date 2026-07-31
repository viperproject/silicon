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
import viper.silicon.rules.evaluator
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silicon.utils.ast.simplifyVariableName
import viper.silicon.verifier.{MainVerifier, Verifier, WorkerVerifier}
import viper.silver.ast
import viper.silver.ast.{NoPosition, SourcePNodeInfo}
import viper.silver.parser._
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.errors.ContractNotWellformed

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
                          resolver: Resolver,
                          pprogram: PProgram,
                          translator: Translator,
                          mainVerifier: MainVerifier,
                          val config: Config) {

  private val allFailures: List[Failure] =
    (verificationResults filter (_.isInstanceOf[Failure])) map (_.asInstanceOf[Failure])

  private var obl: Option[ProofObligation] = None
  private var originalObl: Option[ProofObligation] = None
  private var currentWorker: Option[WorkerVerifier] = None
  private var lastSolverOptions: Option[String] = None
  private var closed: Boolean = false

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

  def hasDebuggableFailure: Boolean = allFailures.exists(f => debugContextOf(f).isDefined)

  def currentFailureIndex: Option[Int] = currentIndex

  def currentObligation: Option[ObligationModel] = obl.map(buildModel)

  def isClosed: Boolean = closed

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
            new DebugResolver(this.pprogram, this.resolver.names), new DebugTranslator(this.pprogram, translator.getMembers()))
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

  /** Discards all changes made to the current obligation. */
  def reset(): DebugCommandResult = withObligation { (_, msgs) =>
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
    val assumptionE = translateStringToExp(text, o)
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
  def prove(): DebugCommandResult = withObligation { (o, msgs) =>
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

  private def initTypechecker(obl: ProofObligation, failedAssertion: Option[ast.Exp],
                              msgs: mutable.ListBuffer[DebugMessage]): Unit = {
    var failedPExp: Option[PNode] =
      failedAssertion.flatMap(_.info.getUniqueInfo[SourcePNodeInfo] match {
        case Some(info) => Some(info.sourcePNode)
        case _ => None
      })
    while (failedPExp.isDefined && !failedPExp.get.isInstanceOf[PScope]) {
      failedPExp = failedPExp.get.getParent
    }
    if (failedPExp.isDefined) {
      obl.resolver.typechecker.curMember = failedPExp.get.asInstanceOf[PScope]
    } else {
      msgs += DebugMessage.warning("Could not determine the scope for typechecking.")
    }

    obl.resolver.typechecker.debugVariableTypes =
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
    currentWorker = Some(v)
    v.start()
    v.decider.createProver(proverName, userArgsString)
    v.decider.prover.emit(obl.proverEmits)

    obl.preambleAssumptions foreach (a => v.decider.prover.assumeAxioms(a.terms, a.description))

    msgs += DebugMessage.info("Initializing prover...")
    obl.assumptionsExp foreach (debugExp => v.decider.debuggerAssume(debugExp.getAllTerms(new mutable.HashSet()), debugExp))
    obl.copy(v = v)
  }

  /** Parses, typechecks and translates an expression entered by the user. */
  private def translateStringToExp(str: String, obl: ProofObligation): ast.Exp = {
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
        obl.resolver.typechecker.names.check(pexp, None, obl.resolver.typechecker.curMember)
        obl.resolver.typechecker.check(pexp, PPrimitiv(PReserved(PKw.Bool)((NoPosition, NoPosition)))())
      } catch {
        case e: Throwable => throw new RuntimeException(s"Error while typechecking $str: ${e.getMessage}", e)
      }
      if (obl.resolver.messages.nonEmpty) {
        val msg = obl.resolver.messages.mkString("\n\t")
        obl.resolver.names.messages = Seq()
        obl.resolver.typechecker.messages = Seq()
        throw new RuntimeException(s"Error while typechecking:\n\t $msg")
      }
    }

    def translatePExp(pexp: PExp): ast.Exp = {
      try {
        obl.translator.exp(pexp)
      } catch {
        case e: Throwable => throw new RuntimeException(s"Error while translating $str: ${e.getMessage}", e)
      }
    }

    val pexp = parseToPExp()
    typecheckPExp(pexp)
    translatePExp(pexp)
  }

  private def evalAssumption(e: ast.Exp, obl: ProofObligation, isFree: Boolean, v: Verifier,
                             msgs: mutable.ListBuffer[DebugMessage]): Option[(State, Term, ast.Exp, InsertionOrderedSet[DebugExp])] = {
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
        val proved = isFree || resV.decider.prover.assert(resT, None)
        if (proved) {
          msgs += DebugMessage.info("Assumption was added successfully!")
          resV.asInstanceOf[WorkerVerifier].decider.debuggerAssume(Seq(resT), null)
          Some((resS, resT, resE, evalPcs.assumptionExps))
        } else {
          msgs += DebugMessage.error("Fail! Could not prove assumption. Skipping")
          None
        }
      case _ =>
        msgs += DebugMessage.error("Error while evaluating expression: " + verificationResult.toString)
        None
    }
  }
}

object SiliconDebugSession {
  val proverNames: Seq[String] = Seq(Z3ProverStdIO.name, Cvc5ProverStdIO.name)
}
