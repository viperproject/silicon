/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.{Set, toSet}
import viper.silicon.interfaces.PreambleEmitter
import viper.silicon.interfaces.decider.Prover
import viper.silicon.decider.PreambleFileEmitter
import viper.silicon.state.SymbolConvert
import viper.silicon.state.terms

trait SequencesEmitter extends PreambleEmitter

class DefaultSequencesEmitter(prover: => Prover,
                             symbolConverter: SymbolConvert,
                             preambleFileEmitter: PreambleFileEmitter[String, String])
    extends SequencesEmitter {

  private var collectedSorts = Set[terms.sorts.Seq]()

  def sorts = toSet(collectedSorts)

  /* Lifetime */

  def reset() {
    collectedSorts = collectedSorts.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    var sequenceTypes = Set[ast.SeqType]()

    program visit { case t: ast.Typed =>
      /* Process the type itself and its type constituents, but ignore types
       * that use type parameters. The assumption is that the latter are
       * handled by the domain emitter.
       */
      t.typ :: ast.utility.Types.typeConstituents(t.typ) filter (_.isConcrete) foreach {
        case s: ast.SeqType =>
          sequenceTypes += s
//        case s: ast.MultisetType =>
//          /* Sequences depend on multisets */
//          sequenceTypes += ast.SeqType(s.elementType)
        case _ =>
        /* Ignore other types */
      }
    }

    collectedSorts = sequenceTypes map (st => symbolConverter.toSort(st).asInstanceOf[terms.sorts.Seq])
  }

  def declareSorts() {
    collectedSorts foreach (s => prover.declare(terms.SortDecl(s)))
  }

  def declareSymbols() {
    collectedSorts foreach {s =>
      val substitutions = Map("$S$" -> prover.termConverter.convert(s.elementsSort))
      val declarations = "/dafny_axioms/sequences_declarations_dafny.smt2"
      prover.logComment(s"$declarations [${s.elementsSort}]")
      preambleFileEmitter.emitParametricAssertions(declarations, substitutions)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      val substitutions = Map("$S$" -> prover.termConverter.convert(terms.sorts.Int))
      val declarations = "/dafny_axioms/sequences_int_declarations_dafny.smt2"
      prover.logComment(declarations)
      preambleFileEmitter.emitParametricAssertions(declarations, substitutions)
    }
  }

  def emitAxioms() {
    collectedSorts foreach {s =>
      val substitutions = Map("$S$" -> prover.termConverter.convert(s.elementsSort))
      val axioms = "/dafny_axioms/sequences_axioms_dafny.smt2"
      prover.logComment(s"$axioms [${s.elementsSort}]")
      preambleFileEmitter.emitParametricAssertions(axioms, substitutions)
    }

    if (collectedSorts contains terms.sorts.Seq(terms.sorts.Int)) {
      val substitutions = Map("$S$" -> prover.termConverter.convert(terms.sorts.Int))
      val axioms = "/dafny_axioms/sequences_int_axioms_dafny.smt2"
      prover.logComment(axioms)
      preambleFileEmitter.emitParametricAssertions(axioms, substitutions)
    }
  }
}
