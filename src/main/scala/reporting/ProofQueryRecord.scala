// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import viper.silver.ast
import viper.silicon.interfaces.decider.{ProofQueryKind, QueryKind}
import java.util.concurrent.ConcurrentLinkedQueue
import scala.jdk.CollectionConverters._

/**
 * One recorded solver interaction (assert, check, push, or pop) with contextual information.
 *
 * @param kind       Which solver interaction this is — assert, check, push, or pop. See [[QueryKind]].
 *                   `assert` is emitted from [[viper.silicon.decider.Decider#assert]];
 *                   `check` from [[viper.silicon.decider.Decider#check]] or
 *                   [[viper.silicon.decider.Decider#checkSmoke]];
 *                   `push`/`pop` from [[viper.silicon.decider.Decider#pushScope]] /
 *                   [[viper.silicon.decider.Decider#popScope]].
 * @param member     Name of the program member (method/function/predicate/domain) whose
 *                   verification triggered this query, if known.
 * @param pos        Source position of the proof obligation.
 * @param category   Category of the query (see [[ProofQueryKind]]) — e.g. PathInfeasibility for
 *                   smoke checks, FunctionalCorrectness for user assertions, etc.
 * @param durationMs Wall-clock duration in milliseconds (includes prover call only, not
 *                   path-condition trivial-check short-circuit).
 * @param succeeded  Whether the query returned true / Unsat. Always true for push/pop.
 * @param description Optional free-text description of the specific proof obligation,
 *                    populated on demand at call sites where extra clarity is useful.
 */
case class ProofQueryRecord(
  kind:        QueryKind,
  member:      Option[String],
  pos:         ast.Position,
  category:    ProofQueryKind,
  durationMs:  Double,
  succeeded:   Boolean,
  description: Option[String] = None
)

/**
 * Thread-safe global collector for [[ProofQueryRecord]]s.
 *
 * Records are appended concurrently during parallel verification and can be
 * retrieved at the end via [[records]]. Call [[clear]] between verification runs.
 */
object ProofQueryCollector {
  private val _records = new ConcurrentLinkedQueue[ProofQueryRecord]()

  def record(r: ProofQueryRecord): Unit = _records.add(r)

  def records: Seq[ProofQueryRecord] = _records.iterator().asScala.toSeq

  def clear(): Unit = _records.clear()
}
