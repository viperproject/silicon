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

  private var collectedFields = Seq[ast.Field]()
  private var collectedSorts = Set[terms.sorts.FieldValueFunction]()

  def sorts: Set[Sort] = toSet(collectedSorts)
    /* Scala's immutable sets are invariant in their element type, hence
     * Set[FVF] is not a subtype of Set[Sort], although FVF is one of Sort.
     */

  def analyze(program: Program) {
    /* TODO: Would be more efficient to use something like program.findFirst(...) which
     *       aborts the traversal as soon the partial function applies (and returns true).
     *       Alternatively, we could perform the whole traversal but then only record fields
     *       that actually occur under quantifiers.
     */
    program visit {
      case q: ast.Quantified if collectedFields.isEmpty && !q.isPure =>
        collectedFields = program.fields
    }

    collectedSorts = (
        toSet(collectedFields map (f => terms.sorts.FieldValueFunction(symbolConverter.toSort(f.typ))))
      + terms.sorts.FieldValueFunction(terms.sorts.Ref))
  }

  /* Symbols are taken from a file, there currently isn't a way of retrieving them */
  def symbols: Option[Set[Function]] = None

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
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
      val substitutions = Map("$FLD$" -> id, "$S$" -> prover.termConverter.convert(sort))

      val fvfAxioms = "/field_value_functions_axioms.smt2"
      prover.logComment(s"$fvfAxioms [$id]")
      preambleFileEmitter.emitParametricAssertions(fvfAxioms, substitutions)

      if (sort == terms.sorts.Ref) {
        val fvfInverseAxioms = "/field_value_functions_inverse_axioms.smt2"
        prover.logComment(s"$fvfInverseAxioms [$id]")
        preambleFileEmitter.emitParametricAssertions(fvfInverseAxioms, substitutions)
      }
    }
  }

  /* Lifetime */

  def reset() {
    collectedFields = Nil
  }

  def stop() {}
  def start() {}
}



trait InverseFunctionsEmitter extends PreambleEmitter

class DefaultInverseFunctionsEmitter(prover: Prover,
                                     symbolConverter: SymbolConvert,
                                     preambleFileEmitter: PreambleFileEmitter[String, String])
  extends InverseFunctionsEmitter {

  private var collectedSorts = Set[Sort]()

  val sorts: Set[Sort] = Set()
  val symbols: Option[Set[Function]] = None

  def analyze(program: Program): Unit = {
    program visit {
      case q: ast.Quantified if !q.isPure =>
        collectedSorts ++= q.variables.map(lvd => symbolConverter.toSort(lvd.typ))
    }
  }

  def declareSorts() {}

  def declareSymbols() {
    collectedSorts foreach { sort =>
      val substitutions = Map("$S$" -> prover.termConverter.convert(sort))

      val declarations = "/inverse_functions_declarations.smt2"
      prover.logComment(declarations)
      preambleFileEmitter.emitParametricAssertions(declarations, substitutions)
    }
  }

  def emitAxioms() {}

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
  }

  def stop() {}
  def start() {}
}
