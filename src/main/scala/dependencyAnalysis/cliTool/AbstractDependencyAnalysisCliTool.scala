package dependencyAnalysis.cliTool

import dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.dependencyAnalysis.graphInterpretation.DependencyGraphInterpreter
import viper.silicon.dependencyAnalysis.{DependencyAnalysisNode, Final}

trait AbstractDependencyAnalysisCliTool {
	val interpreter: DependencyGraphInterpreter[Final]

	protected def getSourceInfoString(nodes: Set[DependencyAnalysisNode]): String = {
		UserLevelDependencyAnalysisNode.mkUserLevelString(nodes, "\n\t")
	}

	protected def getQueriedNodesFromInput(inputs: Set[String]): Set[DependencyAnalysisNode] = {
		inputs flatMap (input => {
			val parts = input.split("@")
			if(parts.size == 2)
				parts(1).toIntOption.map(interpreter.getNodesByPosition(parts(0), _)).getOrElse(Set.empty)
			else if(parts.size == 1){
				parts(0).toIntOption map interpreter.getNodesByLine getOrElse Set.empty
			}else{
				Set.empty
			}
		})
	}

	protected def measureTime[T](function: => T): (T, Double) = {
		val startAnalysis = System.nanoTime()
		val res = function
		val endAnalysis = System.nanoTime()
		val durationMs = (endAnalysis - startAnalysis) / 1e6
		(res, durationMs)
	}
}


trait DependencyAnalysisCliToolExtension extends AbstractDependencyAnalysisCliTool {
	val name: String
	val commands: List[DependencyAnalysisCliCommand]

	def getInfoString(separator: String): String = s"$name$separator\t${commands.map(_.description).mkString(s"$separator\t")}"

	def visit(inputs: Seq[String]): Unit = commands foreach (_.visit(inputs))
}

trait DependencyAnalysisCliCommand {
	val cmdName: String
	val cmd: Seq[String] => Unit
	val description: String

	def accept(inputs: Seq[String]): Boolean = inputs.nonEmpty && inputs.head.equals(cmdName)

	def visit(inputs: Seq[String]): Unit = if(accept(inputs)) cmd(inputs.tail)

}
