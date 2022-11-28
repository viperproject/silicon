// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package supporters.qps

import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silver.ast.{FieldAccess, Forall}


class HeapFunctionsContributor(preambleReader: PreambleReader[String, String],
                                            symbolConverter: SymbolConverter,
                                            termConverter: TermConverter[String, String, String],
                                            config: Config) {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedFields: InsertionOrderedSet[ast.Resource] = InsertionOrderedSet.empty
  private var collectedSorts: InsertionOrderedSet[sorts.HeapSort] = InsertionOrderedSet.empty
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset(): Unit = {
    collectedFields = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop(): Unit = {}
  def start(): Unit = {}

  /* Functionality */

  def analyze(program: ast.Program): Unit = {
    collectedFields ++= program.fields
    collectedFields ++= program.predicates

    // WARNING: DefaultSetsContributor contributes a sort that is due to QPs over fields

    collectedSorts = (
        collectedFields.map{
          case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
          case _: ast.Predicate => sorts.HeapSort(sorts.Snap)
        }
      + sorts.MaskSort)

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
    val templateFile = "/field_value_functions_declarations.smt2"

    collectedFields map (f => {
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id: $sort]", declarations)
    })
  }

  def generateAxioms: Iterable[PreambleBlock] = {
    val templateFile =
      if (config.disableISCTriggers()) "/field_value_functions_axioms_no_triggers.smt2"
      else "/field_value_functions_axioms.smt2"

    collectedFields map (f => {
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id: $sort]", declarations)
    })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[sorts.FieldValueFunction] = collectedSorts

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
