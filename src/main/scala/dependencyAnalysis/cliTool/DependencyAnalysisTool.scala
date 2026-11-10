// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.cliTool.DependencyGraphImporter.{importGraphFromCsv, importProgram}
import viper.silicon.dependencyAnalysis.graph.AxiomAssumptionNode
import viper.silicon.dependencyAnalysis.graphInterpretation.FinalGraphQueries
import viper.silicon.dependencyAnalysis.{DependencyAnalysisOptions, DependencyAnalysisResult, DependencyGraphJoiner}
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silver.ast

object DependencyAnalysisTool {

  /**
   * This method processes command line arguments to import a dependency graph and execute queries on it.
   *
   * Expected command line arguments:
   *  - `--graphFolder "[PATH_TO_GRAPH]"`: (Required) Specifies the path to the folder containing the dependency graph export files.
   *  - `--cmds "[SEMICOLON_SEPARATED_LIST_OF_QUERIES]"`: (Optional) Specifies a series of commands separated by semicolons.
   *    The supported commands correspond to the ones of the DependencyAnalysisUserTool.
   *    If this argument is not provided, the interactive mode of the DependencyAnalysisUserTool will start instead.
   *
   * @throws IllegalArgumentException if the `--graphFolder` argument is not provided.
   */

  def main(args: Array[String]): Unit = {
    val graphFolder = extractGraphFolderFromArgs(args)
    val graph = importGraphFromCsv(graphFolder)
    // TODO ake: doesn't fully work yet, because the exported program has a different line numbering than the program used for the analysis
    val program = importProgram(graphFolder)

    val queries = new FinalGraphQueries("test", graph, List.empty)
    val userTool = DependencyAnalysisCliTool(queries, program, List.empty, DependencyAnalysisOptions())

    val cmdsIndex = args.indexOf("--cmds")
    val cmds = if (0 <= cmdsIndex && cmdsIndex < args.length - 1) args(cmdsIndex + 1) else ""

    userTool.runCommands(cmds)
  }

  private def extractGraphFolderFromArgs(args: Array[String]): String = {
    val idx = args.indexOf("--graphFolder")
    if (0 <= idx && idx < args.length - 1)
      args(idx + 1)
    else
      throw new IllegalArgumentException("Error: --graphFolder argument is required but not found.")
  }

  def runDependencyAnalysisWorkflow(commands: String, options: DependencyAnalysisOptions, verificationResults: List[VerificationResult], axiomNodes: Iterable[AxiomAssumptionNode], program: ast.Program, inputFile: Option[String]): DependencyAnalysisResult = {
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
