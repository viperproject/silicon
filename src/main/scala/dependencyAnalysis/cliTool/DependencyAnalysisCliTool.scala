package viper.silicon.dependencyAnalysis.cliTool

import dependencyAnalysis.cliTool.{AbstractDependencyAnalysisCliTool, DependencyAnalysisCliToolExtension}
import viper.silicon.dependencyAnalysis._
import viper.silicon.dependencyAnalysis.graphInterpretation.{DependencyAnalysisProgressSupporter, DependencyGraphInterpreter}
import viper.silicon.interfaces.Failure
import viper.silver.ast
import viper.silver.ast.Method

import scala.annotation.tailrec
import scala.io.StdIn.readLine

class DependencyAnalysisCliTool(fullGraphInterpreter: DependencyGraphInterpreter[Final], memberInterpreters: Seq[DependencyGraphInterpreter[IntraProcedural]],
																program: ast.Program, verificationErrors: List[Failure]) extends AbstractDependencyAnalysisCliTool {

	val extensions: List[DependencyAnalysisCliToolExtension] = List(
		new DebugDependencyAnalysisCliExtension(fullGraphInterpreter),
		new BenchmarkDependencyAnalysisCliExtension(fullGraphInterpreter, program)
	)

  private val infoString = "Enter " +
    "\n\t'dep [line numbers]' to print all dependencies of the given line numbers or" +
    "\n\t'downDep [line numbers]' to print all dependents of the given line numbers or" +
    "\n\t'cov [members]' to print proof coverage of given member or" +
    "\n\t'covL member [line numbers]' to print proof coverage of given lines of given member or" +
    "\n\t'progress' to compute the verification progress of the program or" +
    "\n\t'guide' to compute verification guidance or" +
    "\n\t'prune [line numbers]' to prune the program with respect to the given line numbers and export the new program or" +
		(if(extensions.nonEmpty) "\n\t" else "") +
		extensions.map(_.getInfoString("\n\t")).mkString("\n\t") +
    "\n\t'q' to quit"

  def run(): Unit = {
    println("Dependency Analysis Tool started.")
    println(infoString)
    runInternal()
  }

  def run(commandStr: String): Unit = {
    handleUserInput(commandStr)
  }

  @tailrec
  private def runInternal(): Unit = {
    try {
      val userInput = readLine()
      if (userInput.equalsIgnoreCase("q") || userInput.equalsIgnoreCase("quit")) {
        return
      }
      if (userInput.nonEmpty) {
        handleUserInput(userInput)
      } else {
        println(infoString)
      }
    }catch {
      case e: Exception => println("Error:\n" + e.getMessage)
    }
    runInternal()
  }

  private def handleUserInput(userInput: String): Unit = {
    val inputParts = userInput.split(" ").toSeq
    if (inputParts.nonEmpty) {
      inputParts.head.toLowerCase match {
				case "help" => println(infoString)
        case "dep" => handleDependencyQuery(inputParts.tail.toSet)
        case "downdep" => handleDependentsQuery(inputParts.tail.toSet)
        case "coverage" | "cov" => handleProofCoverageQuery(inputParts.tail)
        case "covlines" | "covl" => handleProofCoverageLineQuery(inputParts.tail)
        case "progress" | "prog" => handleVerificationProgressQuery(inputParts.tail)
        case "guidance" | "guide" => handleVerificationGuidanceQuery()
        case "prune" => handlePruningRequest(inputParts.tail)
        case _ => extensions.foreach(_.visit(inputParts))
      }
    } else {
      println("Invalid input."); println(infoString)
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
        val ((coverage, uncoveredSources), time) = measureTime(aa.computeProofCoverage())
        println(s"${aa.getMember.map(_.name).getOrElse("")} (${time}ms)")
        println(s"coverage: $coverage")
        if (!coverage.equals(1.0))
          println(s"uncovered nodes:\n\t${uncoveredSources.mkString("\n\t")}")
          println(s"#uncovered nodes:\n\t${uncoveredSources.size}")
      })
    println("Done.")
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
        val ((coverage, uncoveredSources), time) = if(lines.nonEmpty){
          val assertions = lines flatMap aa.getNodesByLine
          measureTime(aa.computeProofCoverage(assertions.toSet))
        }else{
          measureTime(aa.computeProofCoverage())
        }
        println(s"${aa.getMember.map(_.name).getOrElse("")}  (${time}ms)")
        println(s"coverage: $coverage")
        if (!coverage.equals(1.0))
          println(s"uncovered nodes:\n\t${uncoveredSources.mkString("\n\t")}")
          println(s"#uncovered nodes:\n\t${uncoveredSources.size}")
      })
    println("Done.")
  }

  private def handleVerificationProgressQuery(inputs: Seq[String]): Unit = {
		val enableDebugging = inputs.nonEmpty && inputs.head.equals("debug")

    val ((optProgressPeter, optProgressLea), optTime) = measureTime(fullGraphInterpreter.progressSupporter.computeVerificationProgress(enableDebugging))

    println(s"Peter: $optProgressPeter; Lea: $optProgressLea")
    println(s"Finished in ${optTime}ms")
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

    if(queriedAssertions.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)) println("\nQueried assertions (partially) FAILED!\n")
    println("Done.")
  }

  private def handleDependentsQuery(inputs: Set[String]): Unit = {

    val queriedNodes = getQueriedNodesFromInput(inputs).intersect(fullGraphInterpreter.getNonInternalAssumptionNodes)

    val (allDependents, timeAll) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependents(queriedNodes.map(_.id)))
    val (dependentsWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependents(queriedNodes.map(_.id), includeInfeasibilityNodes=false))
    val (explicitDependents, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllExplicitDependents(queriedNodes.map(_.id)))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")

    println(s"\nAll Dependents (${timeAll}ms):\n\t${getSourceInfoString(allDependents)}")
    println(s"\nDependents without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(dependentsWithoutInfeasibility)}")
    println(s"\nExplicit Dependents (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependents)}")
    println("Done.")
  }

  private def handlePruningRequest(inputs: Seq[String]): Unit = {
    println("exportFileName: ")
    val exportFileName = readLine()
    val queriedNodes = getQueriedNodesFromInput(inputs.toSet)
		fullGraphInterpreter.pruningSupporter.pruneProgramAndExport(queriedNodes, program, exportFileName)
    println("Done.")
  }

  private def handleVerificationGuidanceQuery(): Unit = {

    val assumptionRanking = fullGraphInterpreter.progressSupporter.computeAssumptionRanking().filter(_._2 > 0.0)
    println(s"Assumptions/unverified assertions and the number of dependents:\n\t${assumptionRanking.mkString("\n\t")}\n")

    println("Uncovered source code per method: ")
    val memberCoverageRanking = memberInterpreters.filter(mInterpreter => mInterpreter.getMember.isDefined && mInterpreter.getMember.get.isInstanceOf[Method])
      .map(mInterpreter => (mInterpreter.getMember.get.name, new DependencyAnalysisProgressSupporter(mInterpreter).computeUncoveredStatements()))
      .toList.filter(_._2 > 0).sortBy(_._2).reverse
    println(s"\nMethods and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n")
  }

	override val interpreter: DependencyGraphInterpreter[Final] = fullGraphInterpreter
}

