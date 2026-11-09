// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis.graphInterpretation.{FinalGraphQueries, DependencyGraphTestSupporter}

/**
 * [[DependencyGraphTestSupporter]] fails with an assertion at the end of a test run, so these commands write to the
 * console while they run instead of returning a result, which would lose the findings reported before the failure.
 */
class TestDependencyAnalysisCliExtension(queries: FinalGraphQueries, console: DependencyAnalysisCliConsole) extends DependencyAnalysisCliToolExtension{
  override val name: String = "Test Features"
  override val commands: List[DependencyAnalysisCliCommand] = List(
    new TestAllCommand,
    new NodeTypeTestCommand,
    new DependenciesTestCommand,
  )

  private class TestAllCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "test"
    override val description: String = s"""'$cmdName' to test all node types and dependencies with respect to the @dependencyInfo(...) annotations"""
    override val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult = { _ =>
      val testSupporter = new DependencyGraphTestSupporter(queries, console.printLine)
      if (queries.getAssertionNodesWithFailures.nonEmpty) console.printLine(s"Program contains verification failures at \n\t${queries.getAssertionNodesWithFailures.mkString("\n\t")}")
      testSupporter.testDependencies()
      testSupporter.testNodeTypes()
      DependencyAnalysisCliResult.empty
    }
  }

  private class NodeTypeTestCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "testNodeTypes"
    override val description: String = s"""'$cmdName [line numbers]' to test the node type with respect to the @dependencyInfo(...) annotations"""
    override val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult = { input =>
      val testSupporter = new DependencyGraphTestSupporter(queries, console.printLine)
      if (input.args.isEmpty)
        testSupporter.testNodeTypes()
      else
        input.args.flatMap(_.toIntOption).foreach(line => testSupporter.testNodeTypes(queries.getNodesByLine(line)))
      DependencyAnalysisCliResult.empty
    }
  }

  private class DependenciesTestCommand extends DependencyAnalysisCliCommand {
    override val cmdName: String = "testDependencies"
    override val description: String = s"""'$cmdName [line numbers]' to test the node type with respect to the @dependencyInfo(...) annotations"""
    override val cmd: DependencyAnalysisCliInput => DependencyAnalysisCliResult = { input =>
      val testSupporter = new DependencyGraphTestSupporter(queries, console.printLine)
      if (input.args.isEmpty)
        testSupporter.testDependencies()
      else
        input.args.flatMap(_.toIntOption).foreach(line => {
          val testResult = UserLevelDependencyAnalysisNode.from(queries.getNodesByLine(line)) map testSupporter.testDependencies
          val resultStr = if (testResult.forall(_.isEmpty)) "Skipped."
            else if (testResult.forall(test => test.isEmpty || test.get)) "Passed."
            else "Failed."
          console.printLine(s"Line $line: $resultStr")
        })
      DependencyAnalysisCliResult.empty
    }
  }
}
