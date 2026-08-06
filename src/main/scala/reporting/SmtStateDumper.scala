// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

package viper.silicon.reporting

import java.nio.file.{Files, Paths, StandardOpenOption}
import java.util.concurrent.atomic.AtomicInteger
import scala.util.control.NonFatal
import viper.silicon.interfaces.SiliconSmtStateContext
import viper.silicon.verifier.Verifier
import viper.silver.verifier.VerificationError

/* Writes each failure's SiliconSmtStateContext to disk when --smtStateOnError
 * is active and no frontend consumes the context programmatically (e.g. raw
 * Viper input). Two files per failure:
 *   smtstate-<n>-<pos>.txt   readable bundle (goal, assumptions, state, ...)
 *   smtstate-<n>-<pos>.smt2  the prover emits verbatim (replayable session,
 *                            includes the failing query and its trailing pop)
 * Dump failures are swallowed: dumping must never break verification. */
object SmtStateDumper {
  private val counter = new AtomicInteger(0)

  def dump(error: VerificationError, ctx: SiliconSmtStateContext): Unit = {
    try {
      val n = counter.incrementAndGet()
      val pos = error.pos.toString.replaceAll("[^A-Za-z0-9_.@-]", "_")
      val dir = Paths.get(Verifier.config.smtStateDir())
      Files.createDirectories(dir)
      val base = s"smtstate-$n-$pos"

      val sb = new StringBuilder
      def section(title: String)(body: => Unit): Unit = {
        sb.append(s"\n=== $title ===\n"); body
      }
      sb.append(s"${error.fullId} at ${error.pos}\n")
      sb.append(error.readableMessage(false, true)).append('\n')
      section("failed assertion (term)") { sb.append(ctx.failedAssertion).append('\n') }
      ctx.reasonUnknown.foreach(r => section("reason unknown") { sb.append(r).append('\n') })
      section("branch conditions (terms)") {
        ctx.branchConditions.foreach(bc => sb.append(bc).append('\n'))
      }
      section("assumptions (terms)") { ctx.assumptions.foreach(a => sb.append(a).append('\n')) }
      ctx.state.foreach { s =>
        section("store") { s.g.termValues.foreach { case (lv, t) => sb.append(s"$lv -> $t\n") } }
        section("heap") { s.h.values.foreach(ch => sb.append(ch).append('\n')) }
        section("old heaps") {
          s.oldHeaps.foreach { case (l, h) => sb.append(s"-- $l\n"); h.values.foreach(ch => sb.append(ch).append('\n')) }
        }
      }
      section("macro decls") { ctx.macroDecls.foreach(m => sb.append(m).append('\n')) }
      section("function decls") { ctx.functionDecls.foreach(f => sb.append(f).append('\n')) }
      section("preamble assumptions") { ctx.preambleAssumptions.foreach(a => sb.append(a).append('\n')) }

      Files.write(dir.resolve(s"$base.txt"),
        sb.toString.getBytes("UTF-8"),
        StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
      Files.write(dir.resolve(s"$base.smt2"),
        ctx.proverEmits.mkString("\n").getBytes("UTF-8"),
        StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
    } catch {
      case NonFatal(_) => /* never break verification over a dump */
    }
  }
}
