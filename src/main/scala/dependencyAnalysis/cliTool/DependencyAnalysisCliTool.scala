package viper.silicon.dependencyAnalysis.cliTool

import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyAnalysisProgressSupporter, DependencyGraphInterpreter}
import viper.silicon.interfaces.Failure
import viper.silver.ast

import java.io.PrintWriter
import scala.annotation.tailrec
import scala.io.StdIn.readLine

class DependencyAnalysisCliTool(fullGraphInterpreter: DependencyGraphInterpreter[Final],
                                program: ast.Program, verificationErrors: List[Failure]) extends AbstractDependencyAnalysisCliTool {

  val extensions: List[DependencyAnalysisCliToolExtension] = List(
    new DebugDependencyAnalysisCliExtension(fullGraphInterpreter),
    new TestDependencyAnalysisCliExtension(fullGraphInterpreter),
    new BenchmarkDependencyAnalysisCliExtension(fullGraphInterpreter, program)
  )

  def run(commandStr: String): Unit = {
    if (commandStr.equalsIgnoreCase("interactive"))
      handleInteractiveMode()
    else
      handleCommand(commandStr)
  }

  private val infoString = "Enter " +
    "\n\t'dep [line numbers]' to print the direct, explicit, and all dependencies of the given line numbers or" +
    "\n\t'allDeps [line numbers]' (short: 'ad') to print all dependencies of the given line numbers or" +
    "\n\t'downDep [line numbers]' to print the dependents of the given line numbers or" +
    "\n\t'progress' to compute the verification progress of the program or" +
    "\n\t'guide' to compute verification guidance or" +
    "\n\t'prune [line numbers] > [file]' to prune the program with respect to the given line numbers and export the new program to file or" +
    "\n\t'export > [folder]' to export the dependency graph to the given folder or" +
    "\n\t'failures' to print the verification failures or" +
    (if (extensions.nonEmpty) "\n\t" else "") +
    extensions.map(_.getInfoString("\n\t")).mkString("\n\t") +
    "\n\t'q' to quit"

  private def handleInteractiveMode(): Unit = {
    println("Dependency Analysis Tool started.")
    println(infoString)
    if(verificationErrors.nonEmpty || fullGraphInterpreter.getAssertionNodesWithFailures.nonEmpty)
      println("Program did not verify!")

    runInteractiveMode()
  }

  @tailrec
  private def runInteractiveMode(): Unit = {
    try {
      val userInput = readLine()
      if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
        return
      }
      if (userInput.nonEmpty) {
        handleCommand(userInput, isInteractive = true)
      } else {
        println(infoString)
      }
    } catch {
      case e: Exception => println("ERROR:\n\t" + e.getMessage)
      case e: AssertionError => println("ERROR:\n\t" + e.getMessage)
    }
    runInteractiveMode()
  }

  private def handleCommand(cmd: String, isInteractive: Boolean = false): Unit = {
    val exportFileName = cmd.split(">").tail.headOption.map(_.trim)
    val cmdParts = cmd.takeWhile(_ != '>').split(" ").toSeq
    if (cmdParts.nonEmpty) {
      cmdParts.head.toLowerCase match {
        case "help" => println(infoString)
        case "dep" => handleDependencyQuery(cmdParts.tail.toSet)
        case "ad" | "alldeps" => handleAllDependenciesQuery(cmdParts.tail.toSet)
        case "downdep" => handleDependentsQuery(cmdParts.tail.toSet)
        case "export"  => fullGraphInterpreter.exportGraph(program, exportFileName.get)
        case "progress" | "prog" => handleVerificationProgressQuery(cmdParts.tail, exportFileName)
        case "guidance" | "guide" => handleVerificationGuidanceQuery(cmdParts.tail)
        case "prune" => handlePruningRequest(cmdParts.tail, exportFileName.get)
        case "failures" => handleFailuresRequest()
        case _ => extensions.foreach(_.visit(cmdParts))
      }
      println("Done.")
    } else {
      println("Invalid input."); println(infoString)
    }
  }

  private def handleFailuresRequest() = {
    println("Reported verification failures:")
    println(s"\t${verificationErrors.mkString("\n\t")}")
    println(s"Dependency nodes of failures:")
    println(s"\t${fullGraphInterpreter.getAssertionNodesWithFailures.map(_.sourceInfo).mkString("\n\t")}")
  }

  def handleVerificationProgressQuery(inputs: Seq[String], exportFileNameOpt: Option[String] = None): Unit = {
    val enableDebugging = inputs.nonEmpty && inputs.head.equals("debug")

    val ((optProgressPeter, optProgressLea), optTime) = measureTime(fullGraphInterpreter.progressSupporter.computeVerificationProgress(enableDebugging))

    println(s"Peter: ${optProgressPeter.progress}; Lea: ${optProgressLea.progress}\nFinished in ${optTime}ms")

    if (exportFileNameOpt.isDefined) {
      val writer = new PrintWriter(exportFileNameOpt.get)
      writer.println("Spec Quality, Proof Quality (Peter), Progress (Peter), Proof Quality (Lea), Progress (Lea), Runtime [ms]")
      writer.println(s"${optProgressLea.specQuality},${optProgressPeter.proofQuality},${optProgressPeter.progress},${optProgressLea.proofQuality},${optProgressLea.progress},$optTime")
      writer.close()
    }
  }

  private def handleDependencyQuery(inputs: Set[String]): Unit = {
    val queriedNodes = getQueriedNodesFromInput(inputs)
    val queriedAssertions = queriedNodes.filter(node => node.isInstanceOf[GeneralAssertionNode])

    val (directDependencies, timeDirect) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getDirectDependencies(queriedAssertions.map(_.id)))
    val (allDependencies, timeAll) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id)))
    val (allDependenciesWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id), includeInfeasibilityNodes=false))
    val (explicitDependencies, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllExplicitDependencies(queriedAssertions.map(_.id)))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")

    println(s"\nDirect Dependencies (${timeDirect}ms):\n\t${getSourceInfoString(directDependencies.diff(queriedNodes))}")
    println(s"\nAll Dependencies (${timeAll}ms):\n\t${getSourceInfoString(allDependencies.diff(queriedNodes))}")
    println(s"\nDependencies without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(allDependenciesWithoutInfeasibility.diff(queriedNodes))}")
    println(s"\nExplicit Dependencies (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependencies.diff(queriedNodes))}")

    if (queriedAssertions.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)) println("\nQueried assertions (partially) FAILED!\n")

  }

  private def handleAllDependenciesQuery(inputs: Set[String]): Unit = {
    val queriedNodes = getQueriedNodesFromInput(inputs)
    val queriedAssertions = queriedNodes.filter(node => node.isInstanceOf[GeneralAssertionNode])

    val (allDependencies, timeAll) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id)))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")

    println(s"\nAll Dependencies (${timeAll}ms):\n\t${getSourceInfoString(allDependencies.diff(queriedNodes))}")

    if (queriedAssertions.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)) println("\nQueried assertions (partially) FAILED!\n")
  }

  private def handleDependentsQuery(inputs: Set[String]): Unit = {

    val queriedNodes = getQueriedNodesFromInput(inputs).intersect(fullGraphInterpreter.getNonInternalAssumptionNodes)

    val (directDependents, timeDirect) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getDirectDependents(queriedNodes.map(_.id)))
    val (allDependents, timeAll) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependents(queriedNodes.map(_.id)))
    val (dependentsWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependents(queriedNodes.map(_.id), includeInfeasibilityNodes=false))
    val (explicitDependents, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllExplicitDependents(queriedNodes.map(_.id)))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")

    println(s"\nDirect Dependents (${timeDirect}ms):\n\t${getSourceInfoString(directDependents)}")
    println(s"\nAll Dependents (${timeAll}ms):\n\t${getSourceInfoString(allDependents)}")
    println(s"\nDependents without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(dependentsWithoutInfeasibility)}")
    println(s"\nExplicit Dependents (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependents)}")

  }

  def handlePruningRequest(inputs: Seq[String], exportFileName: String): Unit = {
    val queriedNodes = getQueriedNodesFromInput(inputs.toSet)
    fullGraphInterpreter.pruningSupporter.pruneProgramAndExport(queriedNodes, program, exportFileName)
  }

  private def handleVerificationGuidanceQuery(inputs: Seq[String]): Unit = {
    val enableDebugging = inputs.nonEmpty && inputs.head.equals("debug")

    val assumptionRanking = fullGraphInterpreter.progressSupporter.computeAssumptionRanking().filter(_._2 > 0.0)
    println(s"Assumptions/unverified assertions and the number of dependents:\n\t${assumptionRanking.mkString("\n\t")}\n")

    println("Uncovered source code per method: ")
    val uncoveredStatements = new DependencyAnalysisProgressSupporter(fullGraphInterpreter).computeUncoveredStatementsPerMember()

    val memberCoverageRanking = uncoveredStatements.view.mapValues(_.size).toList.filter(_._2 > 0).sortBy(_._2).reverse
    println(s"\nMethods and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n")

    if(enableDebugging)
      println(s"\nUncovered statements by member:\n\t${uncoveredStatements.view.mapValues(v => (v, v.size)).toList.filter(_._2._2 > 0).sortBy(_._2._2).reverse}")

  }

  override val interpreter: DependencyGraphInterpreter[Final] = fullGraphInterpreter
}

