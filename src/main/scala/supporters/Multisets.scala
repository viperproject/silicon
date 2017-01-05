/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{SortDecl, sorts}

trait MultisetsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

/* TODO: Shares a lot of implementation with DefaultSequencesEmitter. Refactor! */

class DefaultMultisetsContributor(preambleReader: PreambleReader[String, String],
                                  symbolConverter: SymbolConverter,
                                  termConverter: TermConverter[String, String, String])
    extends MultisetsContributor[sorts.Multiset, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedSorts: InsertionOrderedSet[sorts.Multiset] = InsertionOrderedSet.empty
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset() {
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def start() {}
  def stop() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    var multisetTypes = InsertionOrderedSet[ast.MultisetType]()

    program visit { case t: ast.Typed =>
      /* Process the type itself and its type constituents, but ignore types
       * that use type parameters. The assumption is that the latter are
       * handled by the domain emitter.
       */
      t.typ :: ast.utility.Types.typeConstituents(t.typ) filter (_.isConcrete) foreach {
        case s: ast.MultisetType =>
          multisetTypes += s
//        case s: ast.SeqType =>
//          /* Sequences depend on multisets */
//          multisetTypes += ast.MultisetType(s.elementType)
        case _ =>
          /* Ignore other types */
      }
    }

    collectedSorts = multisetTypes map (st => symbolConverter.toSort(st).asInstanceOf[sorts.Multiset])
    collectedFunctionDecls = generateFunctionDecls
    collectedAxioms = generateAxioms
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generateFunctionDecls: Iterable[PreambleBlock] = {
    val templateFile = "/dafny_axioms/multisets_declarations_dafny.smt2"

    collectedSorts map {s =>
      val substitutions = Map("$S$" -> termConverter.convert(s.elementsSort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [${s.elementsSort}]", declarations)
    }
  }

  def generateAxioms: Iterable[PreambleBlock] = {
    val templateFile = "/dafny_axioms/multisets_axioms_dafny.smt2"

    collectedSorts map {s =>
      val substitutions = Map("$S$" -> termConverter.convert(s.elementsSort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [${s.elementsSort}]", declarations)
    }
  }

  def sortsAfterAnalysis: InsertionOrderedSet[sorts.Multiset] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  def symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  def axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
