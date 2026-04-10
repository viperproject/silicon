// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.reporting

import viper.silver.ast
import viper.silicon.interfaces.decider.ProofQueryKind
import java.util.concurrent.ConcurrentLinkedQueue
import scala.jdk.CollectionConverters._

/**
 * One recorded SMT query (assert or check) with contextual information.
 *
 * @param isAssert   true  = emitted from [[viper.silicon.decider.Decider#assert]],
 *                   false = emitted from [[viper.silicon.decider.Decider#check]] or
 *                           [[viper.silicon.decider.Decider#checkSmoke]].
 * @param member     Name of the program member (method/function/predicate/domain) whose
 *                   verification triggered this query, if known.
 * @param pos        Source position of the proof obligation.
 * @param kind       Category of the query (see [[ProofQueryKind]]).
 * @param durationMs Wall-clock duration in milliseconds (includes prover call only, not
 *                   path-condition trivial-check short-circuit).
 * @param succeeded  Whether the query returned true / Unsat.
 */
case class ProofQueryRecord(
  isAssert:    Boolean,
  member:      Option[String],
  pos:         ast.Position,
  kind:        ProofQueryKind,
  durationMs:  Double,
  succeeded:   Boolean
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
