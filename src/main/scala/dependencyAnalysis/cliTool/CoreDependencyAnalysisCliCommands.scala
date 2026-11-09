// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.cliTool.DependencyAnalysisCliSupport.{getSourceInfoString, measureTime}
import viper.silicon.dependencyAnalysis.graph._
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyAnalysisProgressSupporter, DependencyAnalysisPruningSupporter, FinalGraphQueries}
import viper.silicon.interfaces.Failure
import viper.silver.ast

import java.io.PrintWriter
import scala.collection.mutable

/**
 * The commands for querying, exporting, and pruning the final dependency graph.
 */
class CoreDependencyAnalysisCliCommands(queries: FinalGraphQueries,
                                        program: ast.Program, verificationErrors: List[Failure]) {

  private lazy val progressSupporter = new DependencyAnalysisProgressSupporter(queries)
  private lazy val pruningSupporter = new DependencyAnalysisPruningSupporter(queries)

  private class CoreCommand(override val cmdName: String, override val description: String,
                            override val aliases: List[String] = List.empty, override val listedInHelp: Boolean = true)
                           (override val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult) extends DependencyAnalysisCliCommand

  val commands: List[DependencyAnalysisCliCommand] = List(
    new CoreCommand("dep", "'dep [line numbers]' to print the direct, explicit, and all dependencies of the given line numbers")(
      input => handleDependencyQuery(input.args.toSet)),
    new CoreCommand("allDeps", "'allDeps [line numbers]' (short: 'ad') to print all dependencies of the given line numbers", aliases = List("ad"))(
      input => handleAllDependenciesQuery(input.args.toSet)),
    new CoreCommand("downDep", "'downDep [line numbers]' to print the dependents of the given line numbers")(
      input => handleDependentsQuery(input.args.toSet)),
    new CoreCommand("progress", "'progress' to compute the verification progress of the program", aliases = List("prog"))(
      input => handleVerificationProgressQuery(input.args, input.exportTarget)),
    new CoreCommand("guide", "'guide' to compute verification guidance", aliases = List("guidance"))(
      input => handleVerificationGuidanceQuery(input.args)),
    new CoreCommand("prune", "'prune [line numbers] > [file]' to prune the program with respect to the given line numbers and export the new program to file")(
      input => handlePruningRequest(input.args, input.exportTarget.get)),
    new CoreCommand("export", "'export > [folder]' to export the dependency graph to the given folder")(
      input => {
        queries.exportGraph(program, input.exportTarget.get)
        DependencyAnalysisCliResult.empty
      }),
    new CoreCommand("failures", "'failures' to print the verification failures")(
      _ => handleFailuresRequest()),
    new CoreCommand("computeGraphOnly", "", listedInHelp = false)(
      _ => DependencyAnalysisCliResult("Command computeGraphOnly executed."))
  )

  private def getQueriedNodesFromInput(inputs: Set[String]): Set[DependencyAnalysisNode] =
    DependencyAnalysisCliSupport.getQueriedNodesFromInput(queries, inputs)

  private def handleFailuresRequest(): DependencyAnalysisCliResult = {
    DependencyAnalysisCliResult(
      "Reported verification failures:",
      s"\t${verificationErrors.mkString("\n\t")}",
      "Dependency nodes of failures:",
      s"\t${queries.getAssertionNodesWithFailures.map(_.sourceInfo).mkString("\n\t")}"
    )
  }

  private def handleVerificationProgressQuery(inputs: Seq[String], exportFileNameOpt: Option[String]): DependencyAnalysisCliResult = {
    val enableDebugging = inputs.nonEmpty && inputs.head.equals("debug")

    val details = mutable.ListBuffer.empty[String]
    val (progress, optTime) = measureTime(progressSupporter.computeVerificationProgress(enableDebugging, details += _))

    if (exportFileNameOpt.isDefined) {
      val writer = new PrintWriter(exportFileNameOpt.get)
      writer.println("Spec Quality, Binary Proof Quality, Binary Progress, Avg Proof Quality, Avg Progress, Runtime [ms]")
      writer.println(s"${progress.specQuality},${progress.binaryProofQuality},${progress.binaryProgress},${progress.avgProofQuality},${progress.avgProgress},$optTime")
      writer.close()
    }

    val summary = s"Binary progress: ${progress.binaryProgress}; Avg progress: ${progress.avgProgress}\nFinished in ${optTime}ms"
    DependencyAnalysisCliResult((details.toSeq :+ summary): _*)
  }

  private def failedAssertionsWarning(queriedAssertions: Set[DependencyAnalysisNode]): Seq[String] = {
    if (queriedAssertions.collect { case n: GeneralAssertionNode => n }.exists(_.hasFailed)) Seq("\nQueried assertions (partially) FAILED!\n")
    else Seq.empty
  }

  private def handleDependencyQuery(inputs: Set[String]): DependencyAnalysisCliResult = {
    val queriedNodes = getQueriedNodesFromInput(inputs)
    val queriedAssertions = queriedNodes.filter(queries.isNonInternalAssertionNode)

    val (directDependencies, timeDirect) = measureTime[Set[DependencyAnalysisNode]](queries.computeDirectDependencies(queriedAssertions))
    val (allDependencies, timeAll) = measureTime[Set[DependencyAnalysisNode]](queries.computeNonInternalDependencies(queriedAssertions))
    val (allDependenciesWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](queries.computeNonInternalDependencies(queriedAssertions, includeInfeasibilityNodes=false))
    val (explicitDependencies, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](queries.computeExplicitDependencies(queriedAssertions))

    val lines = Seq(
      s"Queried:\n\t${getSourceInfoString(queriedNodes)}",
      s"\nDirect Dependencies (${timeDirect}ms):\n\t${getSourceInfoString(directDependencies.diff(queriedNodes))}",
      s"\nAll Dependencies (${timeAll}ms):\n\t${getSourceInfoString(allDependencies.diff(queriedNodes))}",
      s"\nDependencies without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(allDependenciesWithoutInfeasibility.diff(queriedNodes))}",
      s"\nExplicit Dependencies (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependencies.diff(queriedNodes))}"
    ) ++ failedAssertionsWarning(queriedAssertions)
    DependencyAnalysisCliResult(lines: _*)
  }

  private def handleAllDependenciesQuery(inputs: Set[String]): DependencyAnalysisCliResult = {
    val queriedNodes = getQueriedNodesFromInput(inputs)
    val queriedAssertions = queriedNodes.filter(queries.isNonInternalAssertionNode)

    val (allDependencies, timeAll) = measureTime[Set[DependencyAnalysisNode]](queries.computeNonInternalDependencies(queriedAssertions))

    val lines = Seq(
      s"Queried:\n\t${getSourceInfoString(queriedNodes)}",
      s"\nAll Dependencies (${timeAll}ms):\n\t${getSourceInfoString(allDependencies.diff(queriedNodes))}"
    ) ++ failedAssertionsWarning(queriedAssertions)
    DependencyAnalysisCliResult(lines: _*)
  }

  private def handleDependentsQuery(inputs: Set[String]): DependencyAnalysisCliResult = {
    val queriedNodes = getQueriedNodesFromInput(inputs).filter(queries.isNonInternalAssumptionNode)

    val (directDependents, timeDirect) = measureTime[Set[DependencyAnalysisNode]](queries.computeDirectDependents(queriedNodes))
    val (allDependents, timeAll) = measureTime[Set[DependencyAnalysisNode]](queries.computeNonInternalDependents(queriedNodes))
    val (dependentsWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](queries.computeNonInternalDependents(queriedNodes, includeInfeasibilityNodes=false))
    val (explicitDependents, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](queries.computeExplicitDependents(queriedNodes))

    DependencyAnalysisCliResult(
      s"Queried:\n\t${getSourceInfoString(queriedNodes)}",
      s"\nDirect Dependents (${timeDirect}ms):\n\t${getSourceInfoString(directDependents)}",
      s"\nAll Dependents (${timeAll}ms):\n\t${getSourceInfoString(allDependents)}",
      s"\nDependents without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(dependentsWithoutInfeasibility)}",
      s"\nExplicit Dependents (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependents)}"
    )
  }

  private def handlePruningRequest(inputs: Seq[String], exportFileName: String): DependencyAnalysisCliResult = {
    val queriedNodes = getQueriedNodesFromInput(inputs.toSet)
    val messages = mutable.ListBuffer.empty[String]
    pruningSupporter.pruneProgramAndExport(queriedNodes, program, exportFileName, messages += _)
    DependencyAnalysisCliResult(messages.toSeq: _*)
  }

  private def handleVerificationGuidanceQuery(inputs: Seq[String]): DependencyAnalysisCliResult = {
    val enableDebugging = inputs.nonEmpty && inputs.head.equals("debug")

    val assumptionRanking = progressSupporter.computeAssumptionRanking().filter(_._2 > 0.0)
    val uncoveredStatements = progressSupporter.computeUncoveredStatementsPerMember()
    val memberCoverageRanking = uncoveredStatements.view.mapValues(_.size).toList.filter(_._2 > 0).sortBy(_._2).reverse

    val lines = Seq(
      s"Assumptions/unverified assertions and the number of dependents:\n\t${assumptionRanking.mkString("\n\t")}\n",
      "Uncovered source code per method: ",
      s"\nMethods and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n"
    ) ++ (
      if (enableDebugging) Seq(s"\nUncovered statements by member:\n\t${uncoveredStatements.view.mapValues(v => (v, v.size)).toList.filter(_._2._2 > 0).sortBy(_._2._2).reverse}")
      else Seq.empty
    )
    DependencyAnalysisCliResult(lines: _*)
  }
}
