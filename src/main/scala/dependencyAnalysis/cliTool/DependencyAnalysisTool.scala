// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.graph.AxiomAssumptionNode
import viper.silicon.dependencyAnalysis.{DependencyAnalysisOptions, DependencyAnalysisResult, DependencyGraphJoiner}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silver.ast

object DependencyAnalysisTool {

  def runDependencyAnalysisWorkflow(commands: String, options: DependencyAnalysisOptions, verificationResults: List[VerificationResult],
      axiomNodes: Iterable[AxiomAssumptionNode], program: ast.Program, inputFile: Option[String]): DependencyAnalysisResult = {
    val memberResults = verificationResults.flatMap(_.intraproceduralGraphResult)
    val verificationErrors: List[Failure] = (verificationResults filter (_.isInstanceOf[Failure])) map (_.asInstanceOf[Failure])
    // TODO ake: make sure we can access the name of frontend programs (instead of naming it "joined")
    val programName = inputFile.map(_.replaceAll("\\\\", "_").replaceAll("/", "_").replaceAll(".vpr", "")).getOrElse("joined")

    val fullGraphQueries = new DependencyGraphJoiner(programName, memberResults.toSet, axiomNodes, options).joinGraphs()


    val userTool = DependencyAnalysisCliTool(fullGraphQueries, program, verificationErrors, options)
    userTool.runCommands(commands)

    DependencyAnalysisResult(program, fullGraphQueries)
  }
}
