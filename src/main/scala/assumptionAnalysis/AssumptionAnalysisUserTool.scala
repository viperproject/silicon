package silicon.viper.assumptionAnalysis

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisInterpreter, AssumptionAnalysisNode, AssumptionAnalyzer, AssumptionType}

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import viper.silver.ast
import viper.silver.ast.Method

class AssumptionAnalysisUserTool(fullGraphInterpreter: AssumptionAnalysisInterpreter, memberInterpreters: Seq[AssumptionAnalysisInterpreter]) {
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
    memberInterpreters.filter(aa => aa.getMember.isDefined && aa.getMember.exists {
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
    def getSourceInfoString(nodes: Set[AssumptionAnalysisNode]) = {
      nodes.map(_.sourceInfo.getTopLevelSource).toList.sortBy(_.getLineNumber).mkString("\n\t")
    }

    val queriedNodes = lines flatMap fullGraphInterpreter.getNodesByLine
    val directDependencies = getSourceInfoString(fullGraphInterpreter.getDirectDependencies(queriedNodes.map(_.id)))
    val allDependencies = getSourceInfoString(fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id)))
    val explicitDependencies = getSourceInfoString(fullGraphInterpreter.getAllExplicitDependencies(queriedNodes.map(_.id)))
    val dependents = getSourceInfoString(fullGraphInterpreter.getAllNonInternalDependendents(queriedNodes.map(_.id)))

    println(s"Queried:\n\t${queriedNodes.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")

    println(s"\nDirect Dependencies:\n\t$directDependencies")
    println(s"\nAll Dependencies:\n\t$allDependencies")
    println(s"\nExplicit Dependencies:\n\t$explicitDependencies")

    println(s"\nAll Dependents:\n\t$dependents")
    println(s"\nDone.")
  }
}
