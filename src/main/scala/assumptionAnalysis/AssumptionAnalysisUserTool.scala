package silicon.viper.assumptionAnalysis

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisNode, AssumptionAnalyzer, AssumptionType}

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import viper.silver.ast
import viper.silver.ast.Method

class AssumptionAnalysisUserTool(graph: AssumptionAnalysisGraph, assumptionAnalyzers: Seq[AssumptionAnalyzer]) {
  private val infoString = "Enter " +
    "\n\t'dep [line numbers]' to print all dependencies of the given line numbers or" +
    "\n\t'cov [member names]' to print proof coverage of given member names or" +
    "\n\t'q' to quit"

  def run(): Unit = {
    println("Assumption Analysis Tool started.")
    println(infoString)
    runInternal()
  }

  @tailrec
  private def runInternal(): Unit = {
    val userInput = readLine()
    if(userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")){
      return
    }
    if(userInput.nonEmpty) {
      handleUserInput(userInput)
    }else{
      println(infoString)
    }

    runInternal()
  }

  private def handleUserInput(userInput: String): Unit = {
    val inputParts = userInput.split(" ")
    if (inputParts(0).equalsIgnoreCase("d") || inputParts(0).equalsIgnoreCase("dep")) {
      val lines = inputParts.tail.flatMap(_.toIntOption).toSet
      handleDependencyQuery(lines)
    } else if (inputParts(0).equalsIgnoreCase("coverage") || inputParts(0).equalsIgnoreCase("cov")) {
      handleProofCoverageQuery(inputParts.tail)
    } else {
      println("Invalid input.")
      println(infoString)
    }
  }

  private def handleProofCoverageQuery(memberNames: Seq[String]): Unit = {
    println("Proof Coverage")
    assumptionAnalyzers.filter(aa => aa.getMember.isDefined && aa.getMember.exists {
        case meth: Method => meth.body.isDefined && (memberNames.isEmpty || memberNames.contains(meth.name))
        case func: ast.Function => func.body.isDefined && (memberNames.isEmpty || memberNames.contains(func.name))
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

  private def handleDependencyQuery(lines: Set[Int]): Unit = {
    val queriedNodes = lines flatMap findNodeByLine
    val directDependencies = graph.getDirectDependencies(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)
    val dependencies = graph.getAllNonInternalDependencies(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)
    val dependees = graph.getAllNonInternalDependendees(queriedNodes.map(_.id)).toList.sortBy(_.sourceInfo.getLineNumber)

    println(s"Queried:\n\t${queriedNodes.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")

    println(s"\nDirect Dependencies:\n\t${directDependencies.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nAll Dependencies:\n\t${dependencies.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nExplicit Dependencies:\n\t${dependencies.filter(_.assumptionType.equals(AssumptionType.Explicit)).map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")

    println(s"\nAll Dependees:\n\t${dependees.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")
    println(s"\nDone.")

  }

  private def findNodeByLine(line: Int): Set[AssumptionAnalysisNode] =
    graph.nodes.filter(node => node.sourceInfo.getLineNumber.getOrElse(-1) == line).toSet

}
