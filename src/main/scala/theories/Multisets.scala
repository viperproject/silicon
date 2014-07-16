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

trait MultisetsEmitter extends PreambleEmitter

/* TODO: Shares a lot of implementation with DefaultSequencesEmitter. Refactor! */

class DefaultMultisetsEmitter(prover: Prover,
                              symbolConverter: SymbolConvert,
                              preambleFileEmitter: PreambleFileEmitter[_])
    extends MultisetsEmitter {

  private var collectedSorts = Set[terms.sorts.Multiset]()

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
    var multisetTypes = Set[ast.types.Multiset]()

    program visit { case t: silver.ast.Typed =>
      t.typ :: silver.ast.utility.Types.typeConstituents(t.typ) foreach {
        case s: ast.types.Multiset =>
          multisetTypes += s
        case s: ast.types.Seq =>
          /* Sequences depend on multisets */
          multisetTypes += ast.types.Multiset(s.elementType)
        case _ =>
          /* Ignore other types */
      }
    }

    collectedSorts = multisetTypes map (st => symbolConverter.toSort(st).asInstanceOf[terms.sorts.Multiset])
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedSorts foreach {s =>
      prover.logComment(s"/multisets_declarations_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/multisets_declarations_dafny.smt2", s.elementsSort)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      prover.logComment(s"/multisets_axioms_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/multisets_axioms_dafny.smt2", s.elementsSort)
    }
  }
}
