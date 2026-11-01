// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.supporters.functions

import viper.silver.ast
import viper.silicon.state.IdentifierFactory
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?s`
import viper.silicon.verifier.Verifier
import scala.annotation.unused

/** Encapsulates how heap-dependent functions are axiomatised: which state parameters
  * function symbols take, how their definitional axioms are triggered, and which
  * auxiliary symbols and axioms accompany them. The default encoding passes a single
  * snapshot argument; alternative heap encodings may e.g. pass heap arguments instead.
  */
trait FunctionEncoding {
  /** The formal state parameters of a heap-dependent function, prepended to its value
    * parameters, and quantified over in the function's axioms. */
  def stateArgs(function: ast.Function, program: ast.Program, identifierFactory: IdentifierFactory): Seq[Var]

  /** Post-processes a generated axiom, e.g. to replace state-argument placeholders
    * in recorded terms with the formal state parameters. */
  def adaptAxiom(t: Term, @unused data: FunctionData): Term = t

  /** Additional function symbols to declare for a function (e.g. frame functions). */
  def auxiliaryFunctions(@unused data: FunctionData): Seq[Fun] = Seq()

  /** Additional axioms to emit after a function's well-definedness check
    * (e.g. frame axioms). */
  def auxiliaryAxioms(@unused data: FunctionData): Seq[Term] = Seq()

  /** Additional declarations recorded when a function's well-definedness phase
    * completes (e.g. auxiliary functions introduced while computing frames). */
  def declsAfterWellDefinedness(@unused data: FunctionData): Seq[Decl] = Seq()

  /** The state argument of a predicate-trigger application occurring in a
    * function's axioms. */
  def predicateTriggerStateArg(data: FunctionData,
                               predAcc: ast.PredicateAccess,
                               translator: HeapAccessReplacingExpressionTranslator): Term

  /** The definitional axiom of a function, given the axiom's body and the
    * (already filtered) predicate-trigger applications. */
  def definitionalAxiom(data: FunctionData, body: Term, predicateTriggers: Seq[App]): Term

  /** The translation of a heap-dependent function application occurring inside
    * another function, given the applicable to use, the application's recorded
    * snapshot and its translated value arguments. */
  def translateFunctionApp(fun: Applicable, snap: Term, args: Seq[Term], func: ast.Function, program: ast.Program): Term
}

class DefaultFunctionEncoding extends FunctionEncoding {
  def stateArgs(function: ast.Function, program: ast.Program, identifierFactory: IdentifierFactory): Seq[Var] =
    Seq(`?s`)

  def predicateTriggerStateArg(data: FunctionData,
                               predAcc: ast.PredicateAccess,
                               translator: HeapAccessReplacingExpressionTranslator): Term =
    translator.getOrFail(data.locToSnap, predAcc, Seq(), sorts.Snap,
      Option.when(Verifier.config.enableDebugging())(viper.silver.parser.PUnknown()))

  def definitionalAxiom(data: FunctionData, body: Term, predicateTriggers: Seq[App]): Term = {
    val actualPredicateTriggers =
      predicateTriggers.map(pt => Trigger(Seq(data.triggerFunctionApplication, pt)))
    val allTriggers = Seq(Trigger(data.functionApplication)) ++ actualPredicateTriggers

    Forall(data.arguments, body, allTriggers)
  }

  def translateFunctionApp(fun: Applicable, snap: Term, args: Seq[Term], func: ast.Function, program: ast.Program): Term =
    App(fun, snap +: args)
}
