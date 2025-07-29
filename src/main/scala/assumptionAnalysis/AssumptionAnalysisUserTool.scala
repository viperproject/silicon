package silicon.viper.assumptionAnalysis

import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisInterpreter, AssumptionAnalysisNode, AssumptionAnalyzer, AssumptionType}

import scala.annotation.tailrec
import scala.io.StdIn.readLine
import viper.silver.ast
import viper.silver.ast.Method

class AssumptionAnalysisUserTool(fullGraphInterpreter: AssumptionAnalysisInterpreter, memberInterpreters: Seq[AssumptionAnalysisInterpreter]) {
  private val infoString = "Enter " +
    "\n\t'dep [line numbers]' to print all dependencies of the given line numbers or" +
    "\n\t'cov [members]' to print proof coverage of given member or" +
    "\n\t'covL member [line numbers]' to print proof coverage of given lines of given member or" +
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
      handleDependencyQuery(inputParts.tail.toSet)
    } else if (inputParts(0).equalsIgnoreCase("coverage") || inputParts(0).equalsIgnoreCase("cov")) {
      handleProofCoverageQuery(inputParts.tail)
    }else if (inputParts(0).equalsIgnoreCase("covLines") || inputParts(0).equalsIgnoreCase("covL")) {
      handleProofCoverageLineQuery(inputParts.tail)
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
        val (coverage, uncoveredSources) = aa.computeProofCoverage()
        println(s"${aa.getMember.map(_.name).getOrElse("")}")
        println(s"coverage: $coverage")
        if (!coverage.equals(1.0))
          println(s"uncovered nodes:\n\t${uncoveredSources.mkString("\n\t")}")
        println()
      })
  }

  private def handleProofCoverageLineQuery(memberNames: Seq[String]): Unit = {
    if(memberNames.isEmpty) return // TODO ake: invalid input handling

    println("Proof Coverage")
    val lines = memberNames.tail.flatMap(_.toIntOption)
    memberInterpreters.filter(aa => aa.getMember.isDefined && aa.getMember.exists {
        case meth: Method => meth.body.isDefined && meth.name.equalsIgnoreCase(memberNames.head)
        case func: ast.Function => func.body.isDefined && func.name.equalsIgnoreCase(memberNames.head)
        case _ => false
      })
      .foreach(aa => {
        val (coverage, uncoveredSources) = if(lines.nonEmpty){
          val assertions = lines flatMap aa.getNodesByLine
          aa.computeProofCoverage(assertions.toSet)
        }else{
          aa.computeProofCoverage()
        }
        println(s"${aa.getMember.map(_.name).getOrElse("")}")
        println(s"coverage: $coverage")
        if (!coverage.equals(1.0))
          println(s"uncovered nodes:\n\t${uncoveredSources.mkString("\n\t")}")
        println()
      })
  }

  private def handleDependencyQuery(inputs: Set[String]): Unit = {
    def getSourceInfoString(nodes: Set[AssumptionAnalysisNode]) = {
      nodes.groupBy(node => node.sourceInfo.getTopLevelSource.toString).map{case (_, nodes) => nodes.head.sourceInfo.getTopLevelSource}.toList.sortBy(_.getLineNumber).mkString("\n\t")
    }

    val queriedNodes = inputs flatMap (input => {
      val parts = input.split("@")
      if(parts.size == 2)
        parts(1).toIntOption.map(fullGraphInterpreter.getNodesByPosition(parts(0), _)).getOrElse(Set.empty)
      else if(parts.size == 1){
        parts(0).toIntOption map fullGraphInterpreter.getNodesByLine getOrElse Set.empty
      }else{
        Set.empty
      }
    })
    val directDependencies = getSourceInfoString(fullGraphInterpreter.filterOutNodesBySourceInfo(fullGraphInterpreter.getDirectDependencies(queriedNodes.map(_.id)), queriedNodes.map(_.sourceInfo)))
    val allDependencies = getSourceInfoString(fullGraphInterpreter.filterOutNodesBySourceInfo(fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id)), queriedNodes.map(_.sourceInfo)))
    val allDependenciesWithoutInfeasibility = getSourceInfoString(fullGraphInterpreter.filterOutNodesBySourceInfo(fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id), includeInfeasibilityNodes=false), queriedNodes.map(_.sourceInfo)))
    val explicitDependencies = getSourceInfoString(fullGraphInterpreter.filterOutNodesBySourceInfo(fullGraphInterpreter.getAllExplicitDependencies(queriedNodes.map(_.id)), queriedNodes.map(_.sourceInfo)))
//    val dependents = getSourceInfoString(fullGraphInterpreter.getAllNonInternalDependents(queriedNodes.map(_.id)))

    println(s"Queried:\n\t${queriedNodes.map(_.sourceInfo.getTopLevelSource.toString).mkString("\n\t")}")

    println(s"\nDirect Dependencies:\n\t$directDependencies")
    println(s"\nAll Dependencies:\n\t$allDependencies")
    println(s"\nDependencies without infeasibility:\n\t$allDependenciesWithoutInfeasibility")
    println(s"\nExplicit Dependencies:\n\t$explicitDependencies")

//    println(s"\nAll Dependents:\n\t$dependents") TODO ake
    println(s"\nDone.")
  }
}
