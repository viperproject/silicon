/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper
package silicon
package theories

import interfaces.PreambleEmitter
import interfaces.decider.Prover
import decider.PreambleFileEmitter
import state.SymbolConvert
import state.terms
import terms.{Sort, Function}
import viper.silicon.ast.Program

trait FieldValueFunctionsEmitter extends PreambleEmitter

class DefaultFieldValueFunctionsEmitter(prover: Prover,
                                        symbolConverter: SymbolConvert,
                                        preambleFileEmitter: PreambleFileEmitter[String, String])
    extends FieldValueFunctionsEmitter {

  private var fields: Seq[ast.Field] = Nil

  val sorts: Set[Sort] = Set.empty

  def analyze(program: Program) {
    fields = program.fields /* TODO: Could be more specific here and only consider fields used under quantifiers */
  }

  /* Symbols are taken from a file, there currently isn't a way of retrieving them */
  def symbols: Option[Set[Function]] = None

  def declareSorts() { /* No sorts to declare */ }

  def declareSymbols() {
    fields foreach { f =>
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      prover.logComment(s"/field_value_functions_declarations.smt2 [$id: $sort]")
      preambleFileEmitter.emitParametricAssertions("/field_value_functions_declarations.smt2", substitutions)
    }
  }

  def emitAxioms() {
    fields foreach { f =>
      val id = f.name
      val substitutions = Map("$FLD$" -> id)

      prover.logComment(s"/field_value_functions_axioms.smt2 [$id]")
      preambleFileEmitter.emitParametricAssertions("/field_value_functions_axioms.smt2", substitutions)
    }
  }

  /* Lifetime */

  def reset() {
    fields = Nil
  }

  def stop() {}
  def start() {}
}
