package silicon.viper.assumptionAnalysis

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisNode, AssumptionType}

import scala.annotation.tailrec
import scala.io.StdIn.readLine

class AssumptionAnalysisUserTool(graph: AssumptionAnalysisGraph) {

  def run(): Unit = {
    println("Assumption Analysis Tool started. Enter line number or 'q' to quit.")
    runInternal()
  }

  @tailrec
  private def runInternal(): Unit = {
    val userInput = readLine()
    if(userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")){
      return
    }

    val lineOpt = userInput.toIntOption
    if(lineOpt.isDefined){
      val line = lineOpt.get
      handleQuery(line)
    }else{
      println("Invalid input. Line number expected.")
    }

    runInternal()
  }

  private def handleQuery(line: Int): Unit = {

    val queriedNodes = findNodeByLine(line)
    val directDependencies = graph.getDirectDependencies(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)
    val dependencies = graph.getAllNonInternalDependencies(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)
    val dependees = graph.getAllNonInternalDependendees(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)

    println(s"Queried: ${queriedNodes.map(_.sourceInfo.getTopLevelSource.toString).mkString(", ")}")

    println(s"\nDirect Dependencies: \n\t${directDependencies.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nAll Dependencies: \n\t${dependencies.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nExplicit Dependencies: \n\t${dependencies.filter(_.assumptionType.equals(AssumptionType.Explicit)).map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")

    println(s"\nAll Dependees: \n\t${dependees.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nDone.")

  }

  private def findNodeByLine(line: Int): Set[AssumptionAnalysisNode] =
    graph.nodes.filter(node => node.sourceInfo.getLineNumber.getOrElse(-1) == line).toSet

}
