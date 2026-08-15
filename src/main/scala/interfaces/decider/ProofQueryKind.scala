// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.interfaces.decider

/** Categorises the purpose of an SMT query (assert or check) issued by the verifier. */
sealed trait ProofQueryKind

object ProofQueryKind {
  /** (a) Consistency checks: injectivity of quantified-permission receivers and similar
   *  well-formedness obligations. */
  case object Consistency extends ProofQueryKind

  /** (b) Heap proof obligations: chunk-existence checks, permission-amount checks (including
   *  non-negativity and positivity of permission expressions) during consume/produce
   *  operations, and related heap-access correctness queries. */
  case object Heap extends ProofQueryKind

  /** (c) Functional-correctness queries: pre/postcondition checks, assert-statement assertions,
   *  array-index bounds, divisor non-zero, and similar user-visible proof obligations. */
  case object FunctionalCorrectness extends ProofQueryKind

  /** (d) Path-infeasibility checks: smoke checks and branch-feasibility tests that determine
   *  whether the current execution path is reachable at all. */
  case object PathInfeasibility extends ProofQueryKind

  /** (e) Scope-management operations: push and pop of the prover assertion stack
   *  used to bound the scope of branch assumptions, contract checks, etc. */
  case object ScopeManagement extends ProofQueryKind
}
