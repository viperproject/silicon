package viper.silicon.dependencyAnalysis.graphInterpretation

import viper.silicon.dependencyAnalysis.{DependencyAnalysisNode, Final, UserLevelDependencyAnalysisNode}
import viper.silver.dependencyAnalysis.AssumptionType

class DependencyGraphTestSupporter(interpreter: DependencyGraphInterpreter[Final]) {

	private val assumptionTypeRegex = """assumptionType:([^\s,)\"]+)""".r
	private val assertionTypeRegex = """assertionType:([^\s,)\"]+)""".r
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
		if(dependencyInfoOpt.isEmpty) return None

		val dependencyInfo = dependencyInfoOpt.get
		var isTested = false

		val expectedAssumptionTypeOpt: Option[String] = assumptionTypeRegex.findFirstMatchIn(dependencyInfo).map(_.group(1))
		val isAssumptionTypeCorrect = expectedAssumptionTypeOpt match {
			case Some(expectedTypeStr) =>
				val expectedType = AssumptionType.fromString(expectedTypeStr).get
				isTested = true
				ulNode.assumptionTypes.equals(Set(expectedType))
			case None => true
		}

		val expectedAssertionTypeOpt: Option[String] = assertionTypeRegex.findFirstMatchIn(dependencyInfo).map(_.group(1))
		val isAssertionTypeCorrect = expectedAssertionTypeOpt match {
			case Some(expectedTypeStr) =>
				val expectedType = AssumptionType.fromString(expectedTypeStr).get
				isTested = true
				ulNode.assertionTypes.equals(Set(expectedType))
			case None => true
		}

		printIfFalse(isAssumptionTypeCorrect, s"Wrong assumption type for node ${ulNode.source.toString} having assumption types ${ulNode.assumptionTypes}.")
		printIfFalse(isAssertionTypeCorrect, s"Wrong assertion type for node ${ulNode.source.toString} having assertion types ${ulNode.assertionTypes}.")
		Option.when(isTested)(isAssumptionTypeCorrect && isAssertionTypeCorrect)
	}

	private def printIfFalse(test: Boolean, message: String) =
		if(!test)
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
		if(expectedLabelsOpt.isEmpty) return None
		val expectedLabels = expectedLabelsOpt.get

		val queriedAssertions = assertionNode.lowLevelAssertionNodes
		val allDependencies = interpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id))
		val sourceDependencies = UserLevelDependencyAnalysisNode.from(allDependencies).getSourceSet().diff(UserLevelDependencyAnalysisNode.from(queriedAssertions).getSourceSet())

		val labelsInReportedDeps: Set[Set[String]] = sourceDependencies.map(node => nodeLabelRegex.findAllMatchIn(node.toString).map(_.group(1)).toSet)
		val actualLabelInReportedDeps = labelsInReportedDeps.filter(_.size == 1).flatten

		val isSound = expectedLabels.diff(actualLabelInReportedDeps).isEmpty
		printIfFalse(isSound, s"Missing dependencies for ${assertionNode.source.toString}. Reported dependencies: $actualLabelInReportedDeps")
		Some(isSound)
	}
}
