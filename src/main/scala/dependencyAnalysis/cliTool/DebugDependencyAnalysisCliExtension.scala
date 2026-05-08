package viper.silicon.dependencyAnalysis.cliTool

import dependencyAnalysis.cliTool.{DependencyAnalysisCliCommand, DependencyAnalysisCliToolExtension}
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silver.dependencyAnalysis.AnalysisSourceInfo
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType

class DebugDependencyAnalysisCliExtension(override val interpreter: DependencyGraphInterpreter[Final]) extends DependencyAnalysisCliToolExtension{
	override val name: String = "Debug Features"
	override val commands: List[DependencyAnalysisCliCommand] = List(
																																new AssumptionTypesCommand,
																																new AssertionTypesCommand,
																																new LowLevelNodesCommand
																															)

	class AssumptionTypesCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "assumptionTypes"
		override val cmd: Seq[String] => Unit = { inputs =>
			if(inputs.isEmpty)
				println(getAssumptionTypesPerNode().mkString("\n"))
			else
				inputs.flatMap(_.toIntOption).foreach(i => println(s"$i: ${getAssumptionTypesByLine(i)}"))
		}
		override val description: String = s"'$cmdName [line numbers]' to print the assumption types of all nodes or just the provided lines"

		def getAssumptionTypesByLine(line: Int): Set[AssumptionType] = {
			interpreter.getNodesByLine(line).filter(_.isInstanceOf[GeneralAssumptionNode]).map(_.assumptionType)
		}

		def getAssumptionTypesPerNode(): Map[AnalysisSourceInfo, Set[AssumptionType]] =
			getAssumptionTypesPerNode(interpreter.getAssumptionNodes)

		def getAssumptionTypesPerNode(nodes: Set[DependencyAnalysisNode]): Map[AnalysisSourceInfo, Set[AssumptionType]] =
			nodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.assumptionType)).toMap
	}

	class AssertionTypesCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "assertionTypes"
		override val cmd: Seq[String] => Unit = { inputs =>
			if(inputs.isEmpty)
				println(getAssertionTypesPerNode().mkString("\n"))
			else
				inputs.flatMap(_.toIntOption).foreach(i => println(s"$i: ${getAssertionTypesByLine(i)}"))
		}
		override val description: String = s"'$cmdName [line numbers]' to print the assertion types of all nodes or just the provided lines"

		def getAssertionTypesByLine(line: Int): Set[AssumptionType] = {
			interpreter.getNodesByLine(line).filter(_.isInstanceOf[GeneralAssertionNode]).map(_.assumptionType)
		}

		def getAssertionTypesPerNode(): Map[AnalysisSourceInfo, Set[AssumptionType]] =
			getAssertionTypesPerNode(interpreter.getAssertionNodes)

		def getAssertionTypesPerNode(nodes: Set[DependencyAnalysisNode]): Map[AnalysisSourceInfo, Set[AssumptionType]] =
			nodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.assumptionType)).toMap
	}

	class LowLevelNodesCommand extends DependencyAnalysisCliCommand {
		override val cmdName: String = "lowLevelNodes"
		override val cmd: Seq[String] => Unit = inputs =>
			inputs.flatMap(_.toIntOption).foreach(i => println(s"$i:\n\t${getLowLevelNodesByLine(i).mkString("\n\t")}"))
		override val description: String = s"'$cmdName [line numbers]' to print all low-level nodes of the provided lines"

		override def accept(inputs: Seq[String]): Boolean = super.accept(inputs) && inputs.tail.nonEmpty

		def getLowLevelNodesByLine(line: Int): Set[DependencyAnalysisNode] = {
			interpreter.getNodesByLine(line)
		}
	}
}
