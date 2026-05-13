package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyGraphInterpreter, DependencyGraphTestSupporter}
import viper.silicon.dependencyAnalysis.{Final, UserLevelDependencyAnalysisNode}

class TestDependencyAnalysisCliExtension(override val interpreter: DependencyGraphInterpreter[Final]) extends DependencyAnalysisCliToolExtension{
	override val name: String = "Test Features"
	override val commands: List[DependencyAnalysisCliCommand] = List(
		new NodeTypeTestCommand,
		new DependenciesTestCommand,
	)

	class NodeTypeTestCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "testNodeTypes"
		override val description: String = s"""'$cmdName [line numbers]' to test the node type according to the @dependencyInfo(...) annotation"""
		override val cmd: Seq[String] => Unit = { inputs =>
			try{
				val testSupporter = new DependencyGraphTestSupporter(interpreter)
				if(inputs.isEmpty)
					testSupporter.testNodeTypes()
				else
					inputs.flatMap(_.toIntOption).foreach(line => testSupporter.testNodeTypes(interpreter.getNodesByLine(line)))
			}catch {
				case a: AssertionError => println(a.getMessage)
			}
		}
	}

	class DependenciesTestCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "testDependencies"
		override val description: String = s"""'$cmdName [line numbers]' to test the node type according to the @dependencyInfo(...) annotation"""
		override val cmd: Seq[String] => Unit = { inputs =>
			try{
				val testSupporter = new DependencyGraphTestSupporter(interpreter)
				if(inputs.isEmpty)
					testSupporter.testDependencies()
				else
					inputs.flatMap(_.toIntOption).foreach(line => {
						val testResult = UserLevelDependencyAnalysisNode.from(interpreter.getNodesByLine(line)) map testSupporter.testDependencies
						val resultStr = if(testResult.forall(_.isEmpty)) "Skipped."
							else if(testResult.forall(test => test.isEmpty || test.get)) "Passed."
							else "Failed."
						println(s"Line $line: $resultStr")
					})

			}catch {
				case a: AssertionError => println(a.getMessage)
			}
		}
	}
}
