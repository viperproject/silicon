// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.Config
import viper.silicon.interfaces.Failure
import viper.silicon.state.State
import viper.silicon.verifier.{BaseVerifier, MainVerifier, Verifier}
import viper.silver.ast
import viper.silver.frontend.FrontendStateCache

import scala.collection.mutable

/**
  * A breakpoint as set by the user.
  *
  * @param location the statement the breakpoint stops at, or None if it could not be resolved (yet): breakpoints
  *                 are resolved once the verification has started, since only then is the program known.
  */
case class BreakpointStatus(id: Int, file: String, requestedLine: Int, location: Option[StatementLocation]) {
  def verified: Boolean = location.isDefined
}

/**
  * A breakpoint the user asks for.
  *
  * @param line      the (1-based) line.
  * @param condition a Viper expression; the breakpoint only stops on paths on which it may hold, see
  *                  [[DebugRunController.setBreakpoints]].
  */
case class BreakpointRequest(line: Int, condition: Option[String] = None)

/** Why the verification is paused. */
sealed trait PauseReason

object PauseReason {
  /** Before a statement that the given breakpoints resolved to. */
  case class Breakpoint(ids: Seq[Int]) extends PauseReason
  /** Before a statement, at the end of a step (see [[DebugRunController.step]]). */
  case object Step extends PauseReason
  /** Before a statement, because the user asked to pause (see [[DebugRunController.requestPause]]). */
  case object Pause extends PauseReason
  /** At a verification failure, with its message (see [[DebugRunController.pauseOnFailures]]). */
  case class Failure(message: String) extends PauseReason
}

/** How far a step goes; see [[DebugRunController.step]]. */
sealed trait StepKind

object StepKind {
  case object Over extends StepKind
  case object In extends StepKind
  case object Out extends StepKind
}

/**
  * The verification is paused.
  *
  * @param stmt     the statement the verification is paused before, unless it is paused at a failure.
  * @param position where the verification is paused: at `stmt`, or at the assertion that failed.
  * @param session  a debug session whose current proof obligation is the state the verification is paused in:
  *                 its assumptions, store and heap, and for a failure the assertion that failed. Changes made in
  *                 it never affect the paused verification; they are made on a copy with a prover of its own. The
  *                 session is closed when the verification continues.
  * @param messages what opening the paused state in `session` reported, e.g. why it failed.
  */
class DebugPause(val reason: PauseReason,
                 val stmt: Option[ast.Stmt],
                 val position: Option[DebugSourcePos],
                 val memberName: Option[String],
                 val session: SiliconDebugSession,
                 val messages: Seq[DebugMessage]) {

  def hitBreakpointIds: Seq[Int] = reason match {
    case PauseReason.Breakpoint(ids) => ids
    case _ => Seq.empty
  }
}

/** Receives the events of a [[DebugRunController]]. The callbacks must return promptly. */
trait DebugRunListener {
  /** Called when breakpoints have been resolved against the program, i.e. once the verification has started. */
  def breakpointsChanged(breakpoints: Seq[BreakpointStatus]): Unit

  /** Called on the verifier's thread when the verification pauses; it continues after [[DebugRunController.resume]]. */
  def paused(pause: DebugPause): Unit
}

/**
  * Pauses the symbolic execution at breakpoints, after steps, on request, and at verification failures.
  *
  * When a verifier is about to execute a statement a breakpoint resolved to, it builds a [[DebugPause]] with a
  * debug session for the current state, tells the listener, and blocks until [[resume]], [[step]] or [[abort]]
  * is called. Since Silicon explores the paths of a method one after another, a breakpoint is hit once for every
  * feasible path that reaches it (and a loop body is executed once per path, not once per iteration).
  *
  * Debugging should run with a single verifier (`--numberOfParallelVerifiers 1`): with several, several paths
  * would pause at the same time, but only one pause can be shown.
  */
class DebugRunController(listener: DebugRunListener) extends DebugHook {

  private var nextId = 1
  /** The breakpoints of each (normalized) file, by id, in the order in which the user set them. */
  private val requested = mutable.LinkedHashMap.empty[String, Seq[(Int, BreakpointRequest)]]
  /** The condition of each conditional breakpoint, by id. Read without a lock in [[beforeExec]]. */
  @volatile private var conditions: Map[Int, String] = Map.empty
  private var resolver: Option[BreakpointResolver] = None
  private var mainVerifier: Option[MainVerifier] = None
  private var config: Option[Config] = None
  /** The statement locations to stop at, and the breakpoints stopping there. Read without a lock in [[beforeExec]]. */
  @volatile private var stops: Map[StatementLocation, Seq[Int]] = Map.empty

  /** A step that is in progress: it ends at the next statement that `verifierId` executes and that `ends` accepts. */
  private case class StepRequest(verifierId: String, ends: Int => Boolean)
  @volatile private var stepRequest: Option[StepRequest] = None
  @volatile private var pauseRequested = false
  @volatile private var _pauseOnFailures = false

  private var currentPause: Option[DebugPause] = None
  /** The verifier that is paused, and the depth of the statement it is paused at; see [[step]]. */
  private var pausedIn: Option[(String, Int)] = None
  @volatile private var aborted: Option[String] = None
  /** The statement each verifier executed last, and its location; see [[beforeExec]]. */
  private val lastExecuted = mutable.Map.empty[String, (ast.Stmt, StatementLocation)]

  /**
    * Replaces the breakpoints of `file`.
    *
    * A breakpoint with a condition stops unless the condition is provably false in the state the verification is
    * in: a symbolic state stands for many concrete ones, and the condition may hold in some of them but not in
    * others. A condition that cannot be checked (because it does not typecheck, say) stops, and the pause's
    * messages say why.
    */
  def setBreakpoints(file: String, requests: Seq[BreakpointRequest]): Seq[BreakpointStatus] = synchronized {
    val normalized = StatementLocation.normalize(file)
    val bps = requests.map { r => val id = nextId; nextId += 1; (id, r) }
    requested(normalized) = bps
    updateStops()
    bps.map { case (id, r) => status(normalized, id, r.line) }
  }

  def breakpoints: Seq[BreakpointStatus] = synchronized {
    requested.toSeq.flatMap { case (file, bps) => bps.map { case (id, r) => status(file, id, r.line) } }
  }

  /** Whether the verification pauses at (final) verification failures. */
  def pauseOnFailures: Boolean = _pauseOnFailures

  def pauseOnFailures_=(enabled: Boolean): Unit = _pauseOnFailures = enabled

  def pause: Option[DebugPause] = synchronized(currentPause)

  def abortReason: Option[String] = aborted

  /** Lets the paused verification continue. */
  def resume(): Unit = synchronized {
    currentPause.foreach(_.session.close())
    currentPause = None
    notifyAll()
  }

  /**
    * Lets the paused verification continue up to the next statement that the same verifier executes, i.e. on the
    * same path or, once that path has been explored, on the next one:
    *
    *  - [[StepKind.In]] stops at the next statement;
    *  - [[StepKind.Over]] skips the statements of `package` proof scripts that start after the current statement;
    *  - [[StepKind.Out]] also skips the remainder of the proof script the verification is paused in; outside of a
    *    proof script, it continues like [[resume]].
    *
    * Proof scripts are the only statements that contain statements Silicon executes one by one: conditionals
    * and loops become control flow, and method calls are verified modularly. Breakpoints and failures (if
    * [[pauseOnFailures]]) still stop the verification before the step ends.
    */
  def step(kind: StepKind): Unit = synchronized {
    stepRequest = pausedIn.flatMap { case (verifierId, depth) =>
      val ends: Option[Int => Boolean] = kind match {
        case StepKind.In => Some(_ => true)
        case StepKind.Over => Some(_ <= depth)
        case StepKind.Out => Option.when(depth > 0)(_ < depth)
      }
      ends.map(StepRequest(verifierId, _))
    }
    resume()
  }

  /** Pauses the running verification before the next statement any verifier executes. */
  def requestPause(): Unit = pauseRequested = true

  /** Ends the verification: the paused verifier, and every verifier that executes a statement after this, fails. */
  def abort(reason: String): Unit = synchronized {
    if (aborted.isEmpty) aborted = Some(reason)
    resume()
  }

  // --- DebugHook ---------------------------------------------------------------------------------------------

  override def verificationStarted(program: ast.Program, mv: MainVerifier): Unit = {
    val statuses = synchronized {
      resolver = Some(new BreakpointResolver(program))
      mainVerifier = Some(mv)
      config = Some(mv match {
        case b: BaseVerifier => b.config
        case _ => Verifier.config
      })
      updateStops()
      breakpoints
    }
    listener.breakpointsChanged(statuses)
  }

  override def beforeExec(s: State, stmt: ast.Stmt, v: Verifier): Unit = {
    aborted.foreach(r => throw new DebugRunAborted(r))
    if (!BreakpointResolver.isExecuted(stmt)) return
    val location = StatementLocation.of(stmt).getOrElse(return)

    // Several statements may share a position, e.g. when a plugin desugars one statement into several; stop only
    // at the first of them. The same statement executed again (on another path) is a new stop, though.
    val previous = synchronized(lastExecuted.put(v.uniqueId, (stmt, location)))
    if (previous.exists { case (prevStmt, prevLocation) => prevLocation == location && !(prevStmt eq stmt) }) return

    val ids = stops.getOrElse(location, Seq.empty)
    val stepEnds = stepRequest.exists(r => r.verifierId == v.uniqueId && r.ends(depthOf(location)))
    if (ids.isEmpty && !stepEnds && !pauseRequested) return
    val (mv, cfg) = synchronized((mainVerifier, config)) match {
      case (Some(m), Some(c)) => (m, c)
      case _ => return
    }

    // The state has to be captured here, on the verifier's thread: the path conditions are mutable and change as
    // soon as the verifier continues. The session is only opened if it is needed, since that starts a prover.
    val messages = mutable.ListBuffer.empty[DebugMessage]
    var session: Option[SiliconDebugSession] = None
    def openSession(): SiliconDebugSession = session.getOrElse {
      val opened = newSession(Nil, mv, cfg)
      messages ++= opened.openPausedState(s, v, stmt).messages
      session = Some(opened)
      opened
    }

    val currentConditions = conditions
    val hitIds = ids.filter(id => currentConditions.get(id).forall(c => mayHold(openSession(), c, messages)))
    val reason: Option[PauseReason] =
      if (hitIds.nonEmpty) Some(PauseReason.Breakpoint(hitIds))
      else if (stepEnds) Some(PauseReason.Step)
      else if (pauseRequested) Some(PauseReason.Pause)
      else None
    reason match {
      case Some(r) =>
        // Even if the state cannot be opened, the user asked to stop here; the messages say what went wrong.
        val opened = openSession()
        pauseAt(new DebugPause(r, Some(stmt), DebugSourcePos.from(stmt), s.currentMember.map(_.name), opened,
          messages.toSeq), v.uniqueId, depthOf(location))
      case None =>
        session.foreach(_.close())
    }
  }

  override def failed(s: State, v: Verifier, failure: Failure): Unit = {
    aborted.foreach(r => throw new DebugRunAborted(r))
    if (!_pauseOnFailures) return
    val (mv, cfg) = synchronized((mainVerifier, config)) match {
      case (Some(m), Some(c)) => (m, c)
      case _ => return
    }
    val session = newSession(List(failure), mv, cfg)
    val opened = session.openObligation(0)
    val reason = failure.message.reason
    val depth = synchronized(lastExecuted.get(v.uniqueId)).map { case (_, l) => depthOf(l) }.getOrElse(0)
    pauseAt(new DebugPause(PauseReason.Failure(reason.readableMessage), None, DebugSourcePos.from(reason.pos),
      s.currentMember.map(_.name), session, opened.messages), v.uniqueId, depth)
  }

  // --- Internals ---------------------------------------------------------------------------------------------

  private def status(file: String, id: Int, line: Int): BreakpointStatus =
    BreakpointStatus(id, file, line, resolver.flatMap(_.resolve(file, line)))

  private def updateStops(): Unit = {
    stops = resolver match {
      case None => Map.empty
      case Some(r) =>
        requested.toSeq
          .flatMap { case (file, bps) => bps.flatMap { case (id, req) => r.resolve(file, req.line).map(_ -> id) } }
          .groupMap(_._1)(_._2)
    }
    conditions = requested.values.flatten.collect { case (id, BreakpointRequest(_, Some(c))) => id -> c }.toMap
  }

  /**
    * Whether `condition` may hold in the state of `session`, i.e. is not provably false. A condition that cannot
    * be checked is treated as holding, with a message why.
    */
  private def mayHold(session: SiliconDebugSession, condition: String, messages: mutable.ListBuffer[DebugMessage]): Boolean = {
    val res = session.assertText(s"!($condition)")
    res.proved match {
      case Some(negationHolds) => !negationHolds
      case None =>
        val reason = res.messages.filter(_.severity == DebugMessageSeverity.Error).map(_.text).mkString(" ")
        messages += DebugMessage.error(s"The breakpoint condition `$condition` could not be checked: $reason")
        true
    }
  }

  private def depthOf(location: StatementLocation): Int = synchronized(resolver).map(_.depth(location)).getOrElse(0)

  private def newSession(failures: List[Failure], mv: MainVerifier, cfg: Config): SiliconDebugSession = {
    val hasFrontendState =
      FrontendStateCache.resolver != null && FrontendStateCache.pprogram != null && FrontendStateCache.translator != null
    new SiliconDebugSession(failures,
      Option.when(hasFrontendState)(FrontendStateCache.resolver),
      Option.when(hasFrontendState)(FrontendStateCache.pprogram),
      Option.when(hasFrontendState)(FrontendStateCache.translator), mv, cfg)
  }

  /** Blocks the calling verifier until the verification continues. */
  private def pauseAt(pause: DebugPause, verifierId: String, depth: Int): Unit = {
    synchronized {
      stepRequest = None
      pauseRequested = false
      currentPause = Some(pause)
      pausedIn = Some((verifierId, depth))
    }
    listener.paused(pause)
    synchronized {
      while (currentPause.contains(pause)) wait()
      pausedIn = None
    }
    aborted.foreach(r => throw new DebugRunAborted(r))
  }
}
