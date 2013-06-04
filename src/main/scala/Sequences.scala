package semper
package silicon

import interfaces.PreambleEmitter
import interfaces.decider.Prover
import decider.PreambleFileEmitter
import state.SymbolConvert
import state.terms

trait SequenceEmitter extends PreambleEmitter

class DefaultSequenceEmitter(prover: Prover,
                             symbolConverter: SymbolConvert,
                             preambleFileEmitter: PreambleFileEmitter[_])
    extends SequenceEmitter {

  private var collectedSorts = Set[terms.sorts.Seq]()

  def sorts = collectedSorts.toSet[terms.Sort]

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
      prover.logComment(s"/sequences_dafny_declarations.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_dafny_declarations.smt2", s.elementsSort)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      prover.logComment(s"/sequences_dafny_declarations.smt2 [Int]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_dafny_declarations_int.smt2", terms.sorts.Int)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      prover.logComment(s"/sequences_dafny_axioms.smt2 [${s.elementsSort}]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_dafny_axioms.smt2", s.elementsSort)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      prover.logComment(s"/sequences_dafny_axioms_int.smt2 [Int]")
      preambleFileEmitter.emitSortParametricAssertions("/sequences_dafny_axioms_int.smt2", terms.sorts.Int)
    }
  }
}