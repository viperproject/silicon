/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon.interfaces

import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.ProverLike

trait PreambleReader[I, O] {
  def readPreamble(resource: I): Iterable[O]
  def readParametricPreamble(resource: String, substitutions: Map[I, O]): Iterable[O]

  def emitPreamble(preamble: Iterable[O], sink: ProverLike): Unit

  def emitPreamble(resource: I, sink: ProverLike): Unit = {
    emitPreamble(readPreamble(resource), sink)
  }

  def emitParametricPreamble(resource: String, substitutions: Map[I, O], sink: ProverLike): Unit
}

trait PreambleContributor[+SO, +SY, +AX] extends StatefulComponent {
  def analyze(program: ast.Program): Unit

  def sortsAfterAnalysis: Iterable[SO]
  def declareSortsAfterAnalysis(sink: ProverLike): Unit

  def symbolsAfterAnalysis: Iterable[SY]
  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit

  def axiomsAfterAnalysis: Iterable[AX]
  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit

  def updateGlobalStateAfterAnalysis(): Unit
}

trait VerifyingPreambleContributor[+SO, +SY, +AX, U <: ast.Node]
    extends PreambleContributor[SO, SY, AX]
       with VerificationUnit[U] {

  def sortsAfterVerification: Iterable[SO]
  def declareSortsAfterVerification(sink: ProverLike): Unit

  def symbolsAfterVerification: Iterable[SY]
  def declareSymbolsAfterVerification(sink: ProverLike): Unit

  def axiomsAfterVerification: Iterable[AX]
  def emitAxiomsAfterVerification(sink: ProverLike): Unit

  def contributeToGlobalStateAfterVerification(): Unit
}
