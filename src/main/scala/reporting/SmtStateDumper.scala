// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

package viper.silicon.reporting

import java.nio.file.{Files, Path, Paths, StandardOpenOption}
import java.util.concurrent.atomic.AtomicInteger
import scala.util.control.NonFatal
import viper.silicon.decider.Decider
import viper.silicon.interfaces.SiliconSmtStateContext
import viper.silicon.interfaces.decider.CheckInfo
import viper.silicon.state.terms.Term
import viper.silicon.verifier.Verifier

/* Writes SMT state bundles into --smtStateDir. Two files per bundle:
 *   <base>.txt   readable bundle (query, assumptions, state, ...)
 *   <base>.smt2  copy of the verifier's prover session log up to and
 *                including the check in question (replayable as-is)
 * Bases:
 *   smtstate-<n>-<class>-<pos>          a failure (--smtStateOnError); class
 *                                       is the failing check's reason
 *                                       (canceled, incomplete, sat, ...) or
 *                                       noquery when the error was raised
 *                                       without a prover query
 *   smtslow-<n>-<verifier>-c<ordinal>   a check whose wall time reached
 *                                       --smtStateSlowMs, whatever its verdict
 * Dump failures are swallowed: dumping must never break verification. */
object SmtStateDumper {
  private val counter = new AtomicInteger(0)

  private def reasonClass(check: Option[CheckInfo]): String = check match {
    case None => "noquery"
    case Some(c) => c.reason match {
      case Some(r) if r.contains("canceled") || r.contains("resource") || r.contains("timeout") => "canceled"
      case Some(r) if r.contains("incomplete") => "incomplete"
      case Some(_) => "unknown"
      case None => c.answer
    }
  }

  private def sanitize(s: String): String = s.replaceAll("[^A-Za-z0-9_.@-]", "_")

  def dump(error: viper.silver.verifier.VerificationError, ctx: SiliconSmtStateContext): Unit = {
    val base = s"smtstate-${counter.incrementAndGet()}-${reasonClass(ctx.failingCheck)}-${sanitize(error.pos.toString)}"
    write(base, ctx.sessionLog.map(Paths.get(_)), Some(ctx.proverEmits)) { sb =>
      sb.append(s"${error.fullId} at ${error.pos}\n")
      sb.append(error.readableMessage(false, true)).append('\n')
      section(sb, "failed assertion (term)")(sb.append(ctx.failedAssertion).append('\n'))
      section(sb, "failing query")(sb.append(ctx.failingCheck.fold("none (error raised without a prover query)")(_.summary)).append('\n'))
      section(sb, "branch conditions (terms)")(ctx.branchConditions.foreach(bc => sb.append(bc).append('\n')))
      section(sb, "assumptions (terms)")(ctx.assumptions.foreach(a => sb.append(a).append('\n')))
      ctx.state.foreach { s =>
        section(sb, "store")(s.g.termValues.foreach { case (lv, t) => sb.append(s"$lv -> $t\n") })
        section(sb, "heap")(s.h.values.foreach(ch => sb.append(ch).append('\n')))
        section(sb, "old heaps") {
          s.oldHeaps.foreach { case (l, h) => sb.append(s"-- $l\n"); h.values.foreach(ch => sb.append(ch).append('\n')) }
        }
      }
      section(sb, "macro decls")(ctx.macroDecls.foreach(m => sb.append(m).append('\n')))
      section(sb, "function decls")(ctx.functionDecls.foreach(f => sb.append(f).append('\n')))
      section(sb, "preamble assumptions")(ctx.preambleAssumptions.foreach(a => sb.append(a).append('\n')))
    }
  }

  /* Called from the decider right after the check; no symbolic State is
   * available at that level, so the bundle carries the query, the path
   * conditions and the session. */
  def dumpSlow(verifierId: String, goal: Term, check: CheckInfo, decider: Decider): Unit = {
    val base = s"smtslow-${counter.incrementAndGet()}-${sanitize(verifierId)}-c${check.ordinal}"
    decider.prover.flushSessionLog()
    write(base, decider.prover.sessionLogPath, None) { sb =>
      sb.append(s"slow check on verifier $verifierId\n")
      section(sb, "query (term)")(sb.append(goal).append('\n'))
      section(sb, "check")(sb.append(check.summary).append('\n'))
      section(sb, "branch conditions (terms)")(decider.pcs.branchConditions.foreach(bc => sb.append(bc).append('\n')))
      section(sb, "assumptions (terms)")(decider.pcs.assumptions.foreach(a => sb.append(a).append('\n')))
      section(sb, "macro decls")(decider.macroDecls.foreach(m => sb.append(m).append('\n')))
      section(sb, "function decls")(decider.functionDecls.foreach(f => sb.append(f).append('\n')))
      section(sb, "preamble assumptions")(decider.prover.preambleAssumptions.foreach(a => sb.append(a).append('\n')))
    }
  }

  private def section(sb: StringBuilder, title: String)(body: => Unit): Unit = {
    sb.append(s"\n=== $title ===\n"); body
  }

  /* The .smt2 is the session log as it stands when called (the check in
   * question is its last check-sat). Falls back to the emit-level stream
   * (not replayable) when no session log exists. */
  private def write(base: String, sessionLog: Option[Path], fallbackEmits: Option[Seq[String]])
                   (body: StringBuilder => Unit): Unit = {
    try {
      val dir = Paths.get(Verifier.config.smtStateDir())
      Files.createDirectories(dir)
      val sb = new StringBuilder
      body(sb)
      sessionLog.foreach { p =>
        val ordinal = "\\(check-sat".r.findAllIn(new String(Files.readAllBytes(p), "UTF-8")).length
        section(sb, "check ordinal in .smt2")(sb.append(ordinal).append('\n'))
      }
      Files.write(dir.resolve(s"$base.txt"), sb.toString.getBytes("UTF-8"),
        StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
      val smt2 = dir.resolve(s"$base.smt2")
      sessionLog match {
        case Some(p) => Files.copy(p, smt2, java.nio.file.StandardCopyOption.REPLACE_EXISTING)
        case None => fallbackEmits.foreach(e => Files.write(smt2, e.mkString("\n").getBytes("UTF-8"),
          StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING))
      }
    } catch {
      case NonFatal(_) => /* never break verification over a dump */
    }
  }
}
