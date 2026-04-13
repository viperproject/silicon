// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.decider

/** Categorises the purpose of an SMT query (assert or check) issued by the verifier. */
sealed trait ProofQueryKind

object ProofQueryKind {
  /** (a) Consistency checks: non-negative/positive permission assertions, injectivity checks
   *  in quantified permissions, and similar well-formedness obligations. */
  case object Consistency extends ProofQueryKind

  /** (b) Heap proof obligations: chunk-existence checks, permission-amount checks during
   *  consume/produce operations, and related heap-access correctness queries. */
  case object Heap extends ProofQueryKind

  /** (c) Functional-correctness queries: pre/postcondition checks, assert-statement assertions,
   *  array-index bounds, divisor non-zero, and similar user-visible proof obligations. */
  case object FunctionalCorrectness extends ProofQueryKind

  /** (d) Axiomatisation queries: consistency of function, domain, or predicate axioms
   *  (rare – axioms are mostly assumed, not asserted). */
  case object Axiomatization extends ProofQueryKind

  /** (e) Path-infeasibility checks: smoke checks and branch-feasibility tests that determine
   *  whether the current execution path is reachable at all. */
  case object PathInfeasibility extends ProofQueryKind

  /** (f) Unknown: used when the purpose of the query does not clearly fall into any of the
   *  above categories, or has not yet been classified. */
  case object Unknown extends ProofQueryKind
}
