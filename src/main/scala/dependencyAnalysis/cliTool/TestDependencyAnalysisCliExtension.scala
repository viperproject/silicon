package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyGraphInterpreter, DependencyGraphTestSupporter}
import viper.silicon.dependencyAnalysis.{Final, UserLevelDependencyAnalysisNode}

class TestDependencyAnalysisCliExtension(override val interpreter: DependencyGraphInterpreter[Final]) extends DependencyAnalysisCliToolExtension{
	override val name: String = "Test Features"
	override val commands: List[DependencyAnalysisCliCommand] = List(
		new TestAllCommand,
		new NodeTypeTestCommand,
		new DependenciesTestCommand,
	)

	class TestAllCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "test"
		override val description: String = s"""'$cmdName' to test all node types and dependencies with respect to the @dependencyInfo(...) annotations"""
		override val cmd: Seq[String] => Unit = { _ =>
			val testSupporter = new DependencyGraphTestSupporter(interpreter)
			if (interpreter.getAssertionNodesWithFailures.nonEmpty) println(s"Program contains verification failures at \n\t${interpreter.getAssertionNodesWithFailures.mkString("\n\t")}")
			testSupporter.testDependencies()
			testSupporter.testNodeTypes()
		}
	}

	class NodeTypeTestCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "testNodeTypes"
		override val description: String = s"""'$cmdName [line numbers]' to test the node type with respect to the @dependencyInfo(...) annotations"""
		override val cmd: Seq[String] => Unit = { inputs =>
			val testSupporter = new DependencyGraphTestSupporter(interpreter)
			if (inputs.isEmpty)
				testSupporter.testNodeTypes()
			else
				inputs.flatMap(_.toIntOption).foreach(line => testSupporter.testNodeTypes(interpreter.getNodesByLine(line)))
		}
	}

	class DependenciesTestCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "testDependencies"
		override val description: String = s"""'$cmdName [line numbers]' to test the node type with respect to the @dependencyInfo(...) annotations"""
		override val cmd: Seq[String] => Unit = { inputs =>
			val testSupporter = new DependencyGraphTestSupporter(interpreter)
			if (inputs.isEmpty)
				testSupporter.testDependencies()
			else
				inputs.flatMap(_.toIntOption).foreach(line => {
					val testResult = UserLevelDependencyAnalysisNode.from(interpreter.getNodesByLine(line)) map testSupporter.testDependencies
					val resultStr = if (testResult.forall(_.isEmpty)) "Skipped."
						else if (testResult.forall(test => test.isEmpty || test.get)) "Passed."
						else "Failed."
					println(s"Line $line: $resultStr")
				})
		}
	}
}
