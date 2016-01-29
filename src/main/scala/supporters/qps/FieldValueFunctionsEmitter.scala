/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters.qps

import viper.silver.ast
import viper.silicon.{Config, Map, toSet, Set}
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.interfaces.PreambleEmitter
import viper.silicon.interfaces.decider.Prover
import viper.silicon.state.terms.{SortDecl, Function, Sort}
import viper.silicon.state.{terms, SymbolConvert}

trait FieldValueFunctionsEmitter extends PreambleEmitter

class DefaultFieldValueFunctionsEmitter(prover: => Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String],
                                        config: Config)
    extends FieldValueFunctionsEmitter {

  private var collectedFields = Set[ast.Field]()
  private var collectedSorts = Set[terms.sorts.FieldValueFunction]()

  def sorts: Set[Sort] = toSet(collectedSorts)
  /* Scala's immutable sets are invariant in their element type, hence
   * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
   */

  def analyze(program: ast.Program) {
    program visit {
      case ast.utility.QuantifiedPermissions.QPForall(_, _, _, f, _, _, _) =>
        collectedFields += f
    }

    collectedSorts = (
        collectedFields.map(f => terms.sorts.FieldValueFunction(symbolConverter.toSort(f.typ)))
      + terms.sorts.FieldValueFunction(terms.sorts.Ref))
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(SortDecl(s)))
  }

  def declareSymbols() {
    collectedFields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      val fvfDeclarations = "/field_value_functions_declarations.smt2"
      prover.logComment(s"$fvfDeclarations [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfDeclarations, substitutions)
    }
  }

  def emitAxioms() {
    /* Axioms that have to be emitted for each field that is dereferenced from
     * a quantified receiver
     */
    collectedFields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val fvfSubstitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))
      val fvfAxioms = if (config.disableISCTriggers()) "/field_value_functions_axioms_no_triggers.smt2" else "/field_value_functions_axioms.smt2"

      prover.logComment(s"$fvfAxioms [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions(fvfAxioms, fvfSubstitutions)
    }
  }

  /* Lifetime */

  def reset() {
    collectedFields = collectedFields.empty
  }

  def stop() {}
  def start() {}
}
