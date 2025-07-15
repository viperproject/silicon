package silicon.viper.assumptionAnalysis

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisNode, AssumptionAnalyzer, AssumptionType}

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import viper.silver.ast
import viper.silver.ast.Method

class AssumptionAnalysisUserTool(graph: AssumptionAnalysisGraph, assumptionAnalyzers: Seq[AssumptionAnalyzer]) {

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
      handleDependencyQuery(line)
    }else if(userInput.equalsIgnoreCase("coverage") || userInput.equalsIgnoreCase("cov")){
      handleProofCoverageQuery()
    }else{
      println("Invalid input. Line number expected.")
    }

    runInternal()
  }

  private def handleProofCoverageQuery(): Unit = {
    println("Proof Coverage")
    assumptionAnalyzers.filter(aa => aa.getMember.isDefined && aa.getMember.exists {
        case meth: Method => meth.body.isDefined
        case func: ast.Function => func.body.isDefined
        case _ => false
      })
      .foreach(aa => {
        val (coverage, uncoveredSources) = aa.computeProofCoverage().get
        println(s"${aa.getMember.map(_.name).getOrElse("")}")
        println(s"coverage: $coverage")
        if (!coverage.equals(1.0))
          println(s"uncovered nodes:\n\t${uncoveredSources.mkString("\n\t")}")
        println()
      })
  }

  private def handleDependencyQuery(line: Int): Unit = {

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
