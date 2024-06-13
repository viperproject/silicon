// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silicon.supporters

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silver.ast
import viper.silver.ast.Program

/**
 * Add function declarations when the proof makes use of MagicWandSnapFunctions (MWSF).
 * Those are used to preserve values across multiple applications of a magic wand, e.g. by using an applying expression.
 *
 * @param preambleReader Reader that returns the content of some given SMT2 files.
 */
class MagicWandSnapFunctionsContributor(preambleReader: PreambleReader[String, String])
  extends PreambleContributor[Sort, String, String] {

  /** File which contains all function declarations in the SMT2 syntax. */
  private val FILE_DECLARATIONS = "/magic_wand_snap_functions_declarations.smt2"

  /** Set for the sort [[viper.silicon.state.terms.sorts.MagicWandSnapFunction]] */
  private var collectedSorts: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty

  /** Set for all function declaration related to [[viper.silicon.state.terms.sorts.MagicWandSnapFunction]] */
  private var collectedFunctionDecls: Iterable[String] = Seq.empty

  /* Functionality */

  /**
   * Add all function declarations when a program contains magic wands.
   *
   * @param program AST of the program to prove.
   */
  override def analyze(program: Program): Unit = {
    // If there are not magic wands, do not add any definitions or axioms
    if (!program.existsDefined { case ast.MagicWand(_, _) => true }) return

    collectedSorts = InsertionOrderedSet(sorts.MagicWandSnapFunction)
    collectedFunctionDecls = preambleReader.readPreamble(FILE_DECLARATIONS)
  }

  /** Sorts to add to the preamble of the SMT proof script. */
  override def sortsAfterAnalysis: Iterable[Sort] = collectedSorts

  /** Add all sorts needed to the preamble using `sink`. */
  override def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  /** Symbols to add to the preamble of the SMT proof script. */
  override def symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  /** Add all symbols needed to the preamble using `sink`. */
  override def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  /** Axioms to add to the preamble of the SMT proof script. Currently, there are none. */
  override def axiomsAfterAnalysis: Iterable[String] = Seq.empty

  /** Add all axioms needed to the preamble using `sink`. Currently, there are none. */
  override def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {}

  /** Helper function to transform the lines returned by the `PreambleReader`. */
  private def extractPreambleLines(lines: Iterable[String]*): Iterable[String] =
    lines.flatten

  /** Helper function to emit all lines using `sink`. */
  private def emitPreambleLines(sink: ProverLike, lines: Iterable[String]*): Unit = {
    lines foreach { declaration =>
      sink.emit(declaration)
    }
  }

  /* Lifetime */

  def reset(): Unit = {
    collectedSorts = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
  }

  def stop(): Unit = {}

  def start(): Unit = {}
}
