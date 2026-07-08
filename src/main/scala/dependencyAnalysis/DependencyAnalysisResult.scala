// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis

import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silver.ast.Program

case class DependencyAnalysisResult(programName: String, program: Program, dependencyGraphInterpreters: Set[DependencyGraphInterpreter[IntraProcedural]]) {

  protected lazy val fullDependencyGraphInterpreter: DependencyGraphInterpreter[Final] =
    DependencyAnalyzer.joinGraphsAndGetInterpreter(programName, dependencyGraphInterpreters)

  def getFullDependencyGraphInterpreter: DependencyGraphInterpreter[Final] = fullDependencyGraphInterpreter

}
