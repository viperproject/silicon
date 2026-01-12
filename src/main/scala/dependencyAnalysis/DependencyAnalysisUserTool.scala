package viper.silicon.dependencyAnalysis

import dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.interfaces.Failure
import viper.silver.ast
import viper.silver.ast.Method

import java.io.PrintWriter
import scala.annotation.tailrec
import scala.io.StdIn.readLine

class DependencyAnalysisUserTool(fullGraphInterpreter: DependencyGraphInterpreter, memberInterpreters: Seq[DependencyGraphInterpreter],
                                 program: ast.Program, verificationErrors: List[Failure]) {
  private val infoString = "Enter " +
    "\n\t'dep [line numbers]' to print all dependencies of the given line numbers or" +
    "\n\t'downDep [line numbers]' to print all dependents of the given line numbers or" +
    "\n\t'hasDep [line numbers]' to print whether there exists any dependency between any pair of the given lines or" +
    "\n\t'cov [members]' to print proof coverage of given member or" +
    "\n\t'covL member [line numbers]' to print proof coverage of given lines of given member or" +
    "\n\t'progress' to compute the verification progress of the program or" +
    "\n\t'guide' to compute verification guidance or" +
    "\n\t'prune [line numbers]' to prune the program with respect to the given line numbers and export the new program or" +
    "\n\t'q' to quit"

  def run(): Unit = {
    println("Dependency Analysis Tool started.")
    println(infoString)
    runInternal()
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
      case e: Exception => println(e.getMessage)
    }
    runInternal()
  }

  private def handleUserInput(userInput: String): Unit = {
    val inputParts = userInput.split(" ").toSeq
    if (inputParts.head.equalsIgnoreCase("dep")) {
      handleDependencyQuery(inputParts.tail.toSet)
    } else if (inputParts.head.equalsIgnoreCase("downDep")) {
      handleDependentsQuery(inputParts.tail.toSet)
    } else if (inputParts.head.equalsIgnoreCase("hasDep")) {
      handleHasDependencyQuery(inputParts.tail.toSet)
    } else if (inputParts.head.equalsIgnoreCase("coverage") || inputParts.head.equalsIgnoreCase("cov")) {
      handleProofCoverageQuery(inputParts.tail)
    }else if (inputParts.head.equalsIgnoreCase("covLines") || inputParts.head.equalsIgnoreCase("covL")) {
      handleProofCoverageLineQuery(inputParts.tail)
    }else if (inputParts.head.equalsIgnoreCase("progress") || inputParts.head.equalsIgnoreCase("prog")) {
        handleVerificationProgressQuery()
    }else if (inputParts.head.equalsIgnoreCase("guidance") || inputParts.head.equalsIgnoreCase("guide")) {
      handleVerificationGuidanceQuery()
    }else if(inputParts.head.equalsIgnoreCase("prune")) {
      handlePruningRequest(inputParts.tail)
    }else if(inputParts.head.equalsIgnoreCase("benchmark")) {
      handleBenchmarkQuery()
    }else if(inputParts.head.equalsIgnoreCase("graphSize")){
      if(inputParts.tail.isEmpty) {
        handleGraphSizeQuery(fullGraphInterpreter)
      }else{
        memberInterpreters.filter(aa => aa.getMember.isDefined && aa.getMember.exists {
            case meth: Method => meth.body.isDefined && inputParts.tail.contains(meth.name)
            case func: ast.Function => func.body.isDefined && inputParts.tail.contains(func.name)
            case _ => false
          })
          .foreach(aa => handleGraphSizeQuery(aa))
      }
    } else {
      println("Invalid input.")
      println(infoString)
    }
  }

  private def handleGraphSizeQuery(interpreter: DependencyGraphInterpreter): Unit = {
    val allAssumptions = interpreter.getNonInternalAssumptionNodes.filter(n => !n.isInstanceOf[AxiomAssumptionNode])
    val assumptions = UserLevelDependencyAnalysisNode.from(allAssumptions)
    val assertions = UserLevelDependencyAnalysisNode.from(interpreter.getNonInternalAssertionNodes)
    val nodes = UserLevelDependencyAnalysisNode.from(interpreter.getNonInternalAssertionNodes.union(allAssumptions))
    println(s"#Assumptions = ${assumptions.size}")
    println(s"#Assertions = ${assertions.size}")
    println(s"#Nodes = ${nodes.size}")
    println("Done.")
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

  private def handleVerificationProgressQuery(): Unit = {
    println("Computing verification progress...")
    val ((progress, _, info), time) = measureTime(fullGraphInterpreter.computeVerificationProgress())
    println(s"Overall verification progress: $progress")
    println(s"$info")
    println(s"Finished in ${time}ms")
  }

  protected def getSourceInfoString(nodes: Set[DependencyAnalysisNode]): String = {
    UserLevelDependencyAnalysisNode.mkUserLevelString(nodes, "\n\t")
  }

  private def getQueriedNodesFromInput(inputs: Set[String]): Set[DependencyAnalysisNode] = {
    inputs flatMap (input => {
      val parts = input.split("@")
      if(parts.size == 2)
        parts(1).toIntOption.map(fullGraphInterpreter.getNodesByPosition(parts(0), _)).getOrElse(Set.empty)
      else if(parts.size == 1){
        parts(0).toIntOption map fullGraphInterpreter.getNodesByLine getOrElse Set.empty
      }else{
        Set.empty
      }
    })
  }

  private def handleDependencyQuery(inputs: Set[String]): Unit = {
    val queriedNodes = getQueriedNodesFromInput(inputs).filter(node => node.isInstanceOf[GeneralAssertionNode])

    val (directDependencies, timeDirect) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getDirectDependencies(queriedNodes.map(_.id)))
    val (allDependencies, timeAll) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id)))
    val (allDependenciesWithoutInfeasibility, timeWithoutInfeasibility) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id), includeInfeasibilityNodes=false))
    val (explicitDependencies, timeExplicit) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllExplicitDependencies(queriedNodes.map(_.id)))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")

    println(s"\nDirect Dependencies (${timeDirect}ms):\n\t${getSourceInfoString(directDependencies)}")
    println(s"\nAll Dependencies (${timeAll}ms):\n\t${getSourceInfoString(allDependencies)}")
    println(s"\nDependencies without infeasibility (${timeWithoutInfeasibility}ms):\n\t${getSourceInfoString(allDependenciesWithoutInfeasibility)}")
    println(s"\nExplicit Dependencies (${timeExplicit}ms):\n\t${getSourceInfoString(explicitDependencies)}")
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

  private def handleHasDependencyQuery(inputs: Set[String]): Unit = {
    val queriedNodes = getQueriedNodesFromInput(inputs)

    val (depExists, time) = measureTime[Boolean](fullGraphInterpreter.hasAnyDependency(queriedNodes))

    println(s"Queried:\n\t${getSourceInfoString(queriedNodes)}")
    println(s"Dependency exists? $depExists")
    println(s"\nDone in ${time}ms.")
  }

  private def measureTime[T](function: => T): (T, Double) = {
    val startAnalysis = System.nanoTime()
    val res = function
    val endAnalysis = System.nanoTime()
    val durationMs = (endAnalysis - startAnalysis) / 1e6
    (res, durationMs)
  }

  private def handlePruningRequest(inputs: Seq[String]): Unit = {
    println("exportFileName: ")
    val exportFileName = readLine()

    val queriedNodes = getQueriedNodesFromInput(inputs.toSet)
    val dependencies = fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id))
    val crucialNodes = queriedNodes ++ dependencies
    println(s"Found ${crucialNodes.size} crucial nodes. Pruning...")

    fullGraphInterpreter.pruneProgramAndExport(crucialNodes, program, exportFileName)
    println("Done.")
  }

  private def handleBenchmarkQuery(): Unit = {
    val N = 12
    var check = true
    println("Result file name: ")
    val exportFileName = readLine()
    val writer = new PrintWriter(exportFileName)
    writer.println("queried line,#lowLevelDeps,#deps,runtimes [ms]")

    while(check){
      println("enter line number(s) for query or 'q' to quit")
      val userInput = readLine()
      if(userInput.equalsIgnoreCase("q")){
        println("Quit.")
        check = false
      }else{
        val inputs = userInput.split(" ").toSet

        val queriedNodes = getQueriedNodesFromInput(inputs)
        var allTimes = Seq.empty[Double]
        var numDeps = 0
        var numLowLevelDeps = 0

        for (_ <- 0 to N) {
          val (allDependencies, time) = measureTime[Set[DependencyAnalysisNode]](fullGraphInterpreter.getAllNonInternalDependencies(queriedNodes.map(_.id)))
          allTimes = allTimes :+ time
          numLowLevelDeps = allDependencies.size
          numDeps = UserLevelDependencyAnalysisNode.from(allDependencies).size
        }

        writer.println(s"$userInput,$numLowLevelDeps,$numDeps,${allTimes.mkString(",")}")
        println(s"Avg: ${allTimes.sum/allTimes.size}")
      }
    }

    writer.close()
  }

  def handleVerificationGuidanceQuery(): Unit = {
    val assumptionRanking = fullGraphInterpreter.computeAssumptionRanking()
    println(s"Assumptions and the number of dependencies:\n\t${assumptionRanking.mkString("\n\t")}\n")

    val memberCoverageRanking = memberInterpreters.filter(mInterpreter => mInterpreter.getMember.isDefined && mInterpreter.getMember.get.isInstanceOf[Method])
      .map(mInterpreter => (mInterpreter.getMember.get.name, mInterpreter.computeUncoveredStatements()))
      .toList.sortBy(_._2).reverse
    println(s"Members and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n")

    val errorRanking = fullGraphInterpreter.computeFailureRanking()
    println(s"Errors:\n\t${errorRanking.mkString("\n\t")}\n")
  }
}
