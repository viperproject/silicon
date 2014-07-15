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

trait SetsEmitter extends PreambleEmitter

/* TODO: Shares a lot of implementation with DefaultSequencesEmitter. Refactor! */

class DefaultSetsEmitter(prover: Prover,
                         symbolConverter: SymbolConvert,
                         preambleFileEmitter: PreambleFileEmitter[_])
    extends SetsEmitter {

  private var collectedSorts = Set[terms.sorts.Set]()

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
    var setTypes = Set[ast.types.Set]()

    program visit { case t: viper.silver.ast.Typed =>
      t.typ :: silver.ast.utility.Types.typeConstituents(t.typ) foreach {
        case s: ast.types.Set =>
          setTypes += s
        case s: ast.types.Multiset =>
          /* Multisets depend on sets */
          setTypes += ast.types.Set(s.elementType)
        case s: ast.types.Seq =>
          /* Sequences depend on multisets, which in turn depend on sets */
          setTypes += ast.types.Set(s.elementType)
        case _ =>
        /* Ignore other types */
      }
    }

    collectedSorts = setTypes map (st => symbolConverter.toSort(st).asInstanceOf[terms.sorts.Set])
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedSorts foreach {s =>
      prover.logComment(s"/sets_declarations_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sets_declarations_dafny.smt2", s.elementsSort)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      prover.logComment(s"/sets_axioms_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sets_axioms_dafny.smt2", s.elementsSort)
    }
  }
}
