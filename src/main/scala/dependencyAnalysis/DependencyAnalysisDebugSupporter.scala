package dependencyAnalysis

import viper.silicon.dependencyAnalysis.{DependencyAnalysisNode, DependencyGraphInterpreter, DependencyGraphState, GeneralAssumptionNode}
import viper.silver.dependencyAnalysis.AnalysisSourceInfo
import viper.silver.dependencyAnalysis.AssumptionType.AssumptionType

import scala.io.StdIn.readLine

class DependencyAnalysisDebugSupporter[T <: DependencyGraphState](interpreter: DependencyGraphInterpreter[T]) {

	def run(): Unit = {
		try {
			val input = readLine().split(" ")
			input.head match {
				case "assumptionTypes" if input.size == 1 =>
					println(getAssumptionTypesPerNode().mkString("\n"))
				case "assumptionTypes" =>
					input.tail.foreach(s => println(s"$s: ${getAssumptionTypesByLine(s.toInt)}"))
				case "lowLevelNodes" =>
					input.tail.foreach(s => println(s"$s:\n\t${getLowLevelNodesByLine(s.toInt).mkString("\n\t")}"))
				case "q" | "quit" => return
			}
		}catch {
			case _: Throwable =>
				println("Invalid input.")
		}
		run()
	}

	def getAssumptionTypesByLine(line: Int): Set[AssumptionType] = {
		interpreter.getNodesByLine(line).filter(_.isInstanceOf[GeneralAssumptionNode]).map(_.assumptionType)
	}

	def getLowLevelNodesByLine(line: Int): Set[DependencyAnalysisNode] = {
		interpreter.getNodesByLine(line)
	}

	def getAssumptionTypesPerNode(): Map[AnalysisSourceInfo, Set[AssumptionType]] =
		getAssumptionTypesPerNode(interpreter.getAssumptionNodes)

	def getAssumptionTypesPerNode(nodes: Set[DependencyAnalysisNode]): Map[AnalysisSourceInfo, Set[AssumptionType]] =
		nodes.groupBy(_.sourceInfo).view.mapValues(_.map(_.assumptionType)).toMap

}
