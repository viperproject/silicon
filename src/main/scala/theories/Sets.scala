package semper
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

  def reset() {
    collectedSorts = collectedSorts.empty
  }

  def analyze(program: ast.Program) {
    var setTypes = Set[ast.types.Set]()

    program visit {
      case t: sil.ast.Typed => t.typ match {
        case s: ast.types.Set => setTypes += s
        // multisets have a dependency on sets
        case s: ast.types.Multiset => setTypes += ast.types.Set(s.elementType)
        // sequences have a dependency on multisets, which have a dependency on sets
        case s: ast.types.Seq => setTypes += ast.types.Set(s.elementType)
        case _ => /* Ignore other types */
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

  def declareSortWrappers() {
    collectedSorts foreach {
      s =>
        prover.logComment(s"/sortwrappers.smt2 Set[${s.elementsSort}}]")
        preambleFileEmitter.emitSortParametricAssertions("/sortwrappers.smt2", s)
    }
  }
}
