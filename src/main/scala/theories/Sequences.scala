package semper
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
                             preambleFileEmitter: PreambleFileEmitter[_])
    extends SequencesEmitter {

  private var collectedSorts = Set[terms.sorts.Seq]()

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
    var sequenceTypes = Set[ast.types.Seq]()

    program visit {
      case t: sil.ast.Typed => t.typ match {
        case s: ast.types.Seq => sequenceTypes += s
        case _ => /* Ignore other types */
      }
    }

    collectedSorts = sequenceTypes map (st => symbolConverter.toSort(st).asInstanceOf[terms.sorts.Seq])
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedSorts foreach {s =>
      prover.logComment(s"/sequences_declarations_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_declarations_dafny.smt2", s.elementsSort)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      prover.logComment("/sequences_int_declarations_dafny.smt2")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_int_declarations_dafny.smt2", terms.sorts.Int)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      prover.logComment(s"/sequences_axioms_dafny.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_axioms_dafny.smt2", s.elementsSort)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      prover.logComment("/sequences_int_axioms_dafny.smt2")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_int_axioms_dafny.smt2", terms.sorts.Int)
    }
  }

  def declareSortWrappers() {
    collectedSorts foreach {
      s =>
      prover.logComment(s"/sortwrappers.smt2 Seq[${s.elementsSort}}]")
      preambleFileEmitter.emitSortParametricAssertions("/sortwrappers.smt2", s)
    }
  }
}
