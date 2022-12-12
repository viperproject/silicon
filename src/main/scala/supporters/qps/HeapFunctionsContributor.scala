// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters.qps

import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.sorts.{PredHeapSort, PredMaskSort}
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast.{FieldAccess, Forall}


class HeapFunctionsContributor(preambleReader: PreambleReader[String, String],
                                            symbolConverter: SymbolConverter,
                                            termConverter: TermConverter[String, String, String],
                                            config: Config)
  extends PreambleContributor[Sort, String, String]{

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedFields: InsertionOrderedSet[ast.Field] = InsertionOrderedSet.empty
  private var collectedPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty

  private var collectedSorts: InsertionOrderedSet[sorts.HeapSort] = InsertionOrderedSet.empty
  private var predicateSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset(): Unit = {
    collectedFields = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
    predicateSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop(): Unit = {}
  def start(): Unit = {}

  /* Functionality */

  def analyze(program: ast.Program): Unit = {
    if (Verifier.config.carbonQPs()) {
      collectedFields ++= program.fields
      collectedPredicates ++= program.predicates

      // WARNING: DefaultSetsContributor contributes a sort that is due to QPs over fields

      collectedSorts = (
        collectedFields.map {
          case f: ast.Field => sorts.HeapSort(symbolConverter.toSort(f.typ))
        }
          + sorts.MaskSort)
      if (collectedPredicates.nonEmpty)
        predicateSorts = InsertionOrderedSet(Seq(PredHeapSort(), PredMaskSort()))

      collectedFunctionDecls = generateFunctionDecls
      collectedAxioms = generateAxioms
    }
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
    // maps
    val mapsFile = "/maps_functions.smt2"
    val mapsResults = collectedSorts.map(heapSort => {
      val sort = heapSort.valueSort
      val substitutions = Map("$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(mapsFile, substitutions)

      (s"$mapsFile [sort: $sort]", declarations)
    })

    // zeroMask
    val maskFile = "/mask_functions.smt2"
    val maskDeclarations = preambleReader.readParametricPreamble(maskFile, Map())
    val maskResult = (s"$maskFile", maskDeclarations)

    val predResults = if (collectedPredicates.nonEmpty) {
      val substitutions = Map("$S$" -> termConverter.convert(sorts.Snap), "$T$" -> "$Pred", termConverter.convert(sorts.Ref) -> termConverter.convert(sorts.Snap))
      val declarations = preambleReader.readParametricPreamble(mapsFile, substitutions)

      val predMapsResult = (s"$mapsFile [Pred]", declarations)

      val predMaskDeclarations = preambleReader.readParametricPreamble(maskFile, Map(termConverter.convert(sorts.Ref) -> termConverter.convert(sorts.Snap), termConverter.convert(sorts.Perm) -> "$PredMask"))
      val predMaskResult = (s"$maskFile", predMaskDeclarations)
      Seq(predMapsResult, predMaskResult)
    } else Seq()

    // wrappers
    val wrapperFile = "/heapwrappers_functions.smt2"
    val wrapperResults = collectedFields.map(resource => {
      val (sort, id) = resource match {
        case f: ast.Field => (symbolConverter.toSort(f.typ), f.name)
      }
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(wrapperFile, substitutions)

      (s"$wrapperFile [id: $id, sort: $sort]", declarations)
    })
    val predWrapperResults = collectedPredicates.map(pred => {
      val substitutions = Map("$FLD$" -> pred.name, "$S$" -> termConverter.convert(sorts.Snap), "$T$" -> "$Pred")
      val declarations = preambleReader.readParametricPreamble(wrapperFile, substitutions)

      (s"$wrapperFile [predicate: $pred.name,]", declarations)
    })


    mapsResults ++ Seq(maskResult) ++ predResults ++ wrapperResults ++ predWrapperResults
  }

  def generateAxioms: Iterable[PreambleBlock] = {
    // maps
    val mapsFile = "/maps_axioms.smt2"
    val mapsResults = collectedSorts.map(heapSort => {
      val sort = heapSort.valueSort
      val substitutions = Map("$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(mapsFile, substitutions)

      (s"$mapsFile [sort: $sort]", declarations)
    })

    // zeroMask
    val maskFile = "/mask_axioms.smt2"
    val maskDeclarations = preambleReader.readParametricPreamble(maskFile, Map())
    val maskResult = (s"$maskFile", maskDeclarations)

    // wrappers
    val wrapperFile = "/heapwrappers_axioms.smt2"
    val wrapperResults = collectedFields.map(resource => {
      val (sort, id) = resource match {
        case f: ast.Field => (symbolConverter.toSort(f.typ), f.name)
        case p: ast.Predicate => (sorts.Snap, p.name)
      }
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort), "$T$" -> termConverter.convertSanitized(sort))
      val declarations = preambleReader.readParametricPreamble(wrapperFile, substitutions)

      (s"$wrapperFile [id: $id, sort: $sort]", declarations)
    })

    mapsResults ++ Seq(maskResult) ++ wrapperResults
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort] = collectedSorts ++ predicateSorts

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
