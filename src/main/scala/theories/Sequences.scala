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

trait SequencesEmitter extends PreambleEmitter

class DefaultSequencesEmitter(prover: Prover,
                             symbolConverter: SymbolConvert,
                             preambleFileEmitter: PreambleFileEmitter[String, String])
    extends SequencesEmitter {

  private var collectedSorts = Set[terms.sorts.Seq]()
  private var programUsesQuantifiedPermissions = false

  def sorts = toSet(collectedSorts)

  /**
   * The symbols are take from a file and it is currently not possible to retrieve a list of
   * symbols that have been declared.
   *
   * @return None
   */
  def symbols = None

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    var sequenceTypes = Set[ast.types.Seq]()

    program visit { case t: silver.ast.Typed =>
      t.typ :: silver.ast.utility.Types.typeConstituents(t.typ) foreach {
        case s: ast.types.Seq =>
          sequenceTypes += s
        case s: ast.types.Multiset =>
          /* Sequences depend on multisets */
          sequenceTypes += ast.types.Seq(s.elementType)
        case _ =>
        /* Ignore other types */
      }
    }

    collectedSorts = sequenceTypes map (st => symbolConverter.toSort(st).asInstanceOf[terms.sorts.Seq])

    programUsesQuantifiedPermissions = program existsDefined { case q: ast.Quantified if !q.isPure => }
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedSorts foreach {s =>
      val substitutions = Map("$S$" -> prover.termConverter.convert(s.elementsSort))
      prover.logComment(s"/sequences_declarations_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitParametricAssertions("/sequences_declarations_dafny.smt2", substitutions)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      val substitutions = Map("$S$" -> prover.termConverter.convert(terms.sorts.Int))
      prover.logComment("/sequences_int_declarations_dafny.smt2")
      preambleFileEmitter.emitParametricAssertions("/sequences_int_declarations_dafny.smt2", substitutions)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      val substitutions = Map("$S$" -> prover.termConverter.convert(s.elementsSort))
      prover.logComment(s"/sequences_axioms_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitParametricAssertions("/sequences_axioms_dafny.smt2", substitutions)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      val substitutions = Map("$S$" -> prover.termConverter.convert(terms.sorts.Int))
      prover.logComment("/sequences_int_axioms_dafny.smt2")
      preambleFileEmitter.emitParametricAssertions("/sequences_int_axioms_dafny.smt2", substitutions)
    }

    if (collectedSorts.nonEmpty && programUsesQuantifiedPermissions) {
      val axioms = "/sequences_inverse_axioms.smt2"
      prover.logComment(axioms)
      preambleFileEmitter.emitParametricAssertions(axioms, Map())
    }
  }
}
