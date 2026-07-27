// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.dependencyAnalysis.graphInterpretation

import viper.silicon.dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis.graph._
import viper.silver.dependencyAnalysis.AssumptionType

import scala.util.matching.Regex

class DependencyGraphTestSupporter(interpreter: DependencyGraphInterpreter[Final]) {

  private val assumptionTypeRegex = """assumptionType:([^\s,)\"]+)""".r
  private val assertionTypeRegex: Regex = """assertionType:([^\s,)\"]+)""".r
  private val nodeLabelRegex = """label:([^\s,)\"]+)""".r
  private val expectedDependenciesRegex = """expectedDependencies:\[([^\]]+)\]""".r
  private val dependencyInfoRegex = """@dependencyInfo\(([^()]*)\)""".r

  def testNodeTypes(): Unit = {
    testNodeTypes(interpreter.getNonInternalAssertionNodes ++ interpreter.getNonInternalAssumptionNodes)
  }

  def testNodeTypes(nodes: Set[DependencyAnalysisNode]): Unit = {
    val userLevelNodes = UserLevelDependencyAnalysisNode.from(nodes)
    val tests = userLevelNodes.toList map testUserLevelNode
    val numExecutedTests = tests.count(_.isDefined)
    val numPassedTests = tests.count(_.getOrElse(false))
    println(s"Node type tests: Passed $numPassedTests/$numExecutedTests tests.")
    assert(numPassedTests == numExecutedTests, s"Node type test failed. Only $numPassedTests/$numExecutedTests tests passed.")
  }

  private def testUserLevelNode(ulNode: UserLevelDependencyAnalysisNode): Option[Boolean] = {
    val dependencyInfoOpt = dependencyInfoRegex.findFirstMatchIn(ulNode.source.toString).map(_.group(1))
    dependencyInfoOpt match {
      case None => None
      case Some(dependencyInfo) =>
        val (isAssumptionTypeCorrect, isTested) = testTypeInternal(dependencyInfo, assumptionTypeRegex, ulNode.assumptionTypes)
        val (isAssertionTypeCorrect, isTested2) = testTypeInternal(dependencyInfo, assertionTypeRegex, ulNode.assertionTypes)

        printIfFalse(isAssumptionTypeCorrect, s"Wrong assumption type for node ${ulNode.source.toString} having assumption types ${ulNode.assumptionTypes}.")
        printIfFalse(isAssertionTypeCorrect, s"Wrong assertion type for node ${ulNode.source.toString} having assertion types ${ulNode.assertionTypes}.")
        Option.when(isTested || isTested2)(isAssumptionTypeCorrect && isAssertionTypeCorrect)
    }
  }


  /* returns (testSucceeded?, tested?) */
  def testTypeInternal(dependencyInfo: String, pattern: Regex, reportedTypes: Set[AssumptionType.AssumptionType]): (Boolean, Boolean) =
    pattern.findFirstMatchIn(dependencyInfo).map(_.group(1)) match {
      case Some(expectedTypeStr) =>
        val expectedTypeOpt = AssumptionType.fromString(expectedTypeStr)
        expectedTypeOpt match {
          case Some(expectedType) =>
            (reportedTypes.filterNot(_.isInstanceOf[AssumptionType.InternalType]).equals(Set(expectedType)), true)
          case None =>
            print(s"ERROR: could not parse assumption type $expectedTypeStr.")
            (false, true)
        }
      case None => (true, false) // not tested
    }

  private def printIfFalse(test: Boolean, message: String): Unit =
    if (!test)
      println(message)

  def testDependencies(): Unit = {
    val testResults = UserLevelDependencyAnalysisNode.from(interpreter.getNonInternalAssertionNodes).toList map testDependencies
    val numExecutedTests = testResults.count(_.isDefined)
    val numPassedTests = testResults.count(_.getOrElse(false))
    println(s"Dependency tests: Passed $numPassedTests/$numExecutedTests tests.")
    assert(numPassedTests == numExecutedTests, s"Dependency test failed. Only $numPassedTests/$numExecutedTests tests passed.")
  }

  def testDependencies(assertionNode: UserLevelDependencyAnalysisNode): Option[Boolean] = {
    val expectedLabelsOpt = expectedDependenciesRegex.findFirstMatchIn(assertionNode.source.toString).map(_.group(1).split(",").map(_.trim).toSet)
    expectedLabelsOpt match {
      case None => None
      case Some(expectedLabels) =>
        val queriedAssertions = assertionNode.lowLevelAssertionNodes
        val allDependencies = interpreter.computeNonInternalDependencies(queriedAssertions.toSet)
        val sourceDependencies = UserLevelDependencyAnalysisNode.from(allDependencies).toSourceSet().diff(UserLevelDependencyAnalysisNode.from(queriedAssertions).toSourceSet())

        val labelsInReportedDeps: Set[Set[String]] = sourceDependencies.map(node => nodeLabelRegex.findAllMatchIn(node.toString).map(_.group(1)).toSet)
        val actualLabelInReportedDeps = labelsInReportedDeps.filter(_.size == 1).flatten

        val labelDiff = expectedLabels.diff(actualLabelInReportedDeps)
        val isSound = labelDiff.isEmpty
        printIfFalse(isSound, s"Missing dependencies (${labelDiff.mkString(", ")}) for ${assertionNode.source.toString}. Reported dependencies: ${actualLabelInReportedDeps.mkString(", ")}")
        Some(isSound)
    }
  }
}
