package viper.silicon.dependencyAnalysis

import dependencyAnalysis.UserLevelDependencyAnalysisNode
import viper.silicon.interfaces.Failure
import viper.silver.ast
import viper.silver.ast.{AbstractAssign, AnnotationInfo, AnonymousDomainAxiom, Apply, Assert, Assume, Exhale, ExtensionStmt, Fold, Goto, If, Inhale, Label, LocalVarDeclStmt, MakeInfoPair, Method, MethodCall, NamedDomainAxiom, NewStmt, Package, Quasihavoc, Quasihavocall, Seqn, Unfold, While}

import java.io.{BufferedWriter, FileWriter, PrintWriter}
import scala.annotation.tailrec
import scala.io.Source
import scala.io.StdIn.readLine
import scala.util.matching.Regex

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
    }else if (inputParts.head.equalsIgnoreCase("progressDebug")) {
      handleVerificationProgressDEBUGQuery()
    }else if (inputParts.head.equalsIgnoreCase("progressNaive")) {
      handleVerificationProgressNaiveQuery()
    }else if (inputParts.head.equalsIgnoreCase("guidance") || inputParts.head.equalsIgnoreCase("guide")) {
      handleVerificationGuidanceQuery()
    }else if (inputParts.head.equalsIgnoreCase("guideOld")) {
      handleVerificationGuidanceOldQuery()
    }else if(inputParts.head.equalsIgnoreCase("prune")) {
      handlePruningRequest(inputParts.tail)
    }else if(inputParts.head.equalsIgnoreCase("benchmark")) {
      handleBenchmarkQuery()
    }else if(inputParts.head.equalsIgnoreCase("precisionEval")) {
      handlePrecisionEval(inputParts.tail)
    }else if(inputParts.head.equalsIgnoreCase("annotate")) {
      handleAnnotateQuery(inputParts.tail)
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
    val allAssumptions = interpreter.getNonInternalAssumptionNodes
    val assumptions = UserLevelDependencyAnalysisNode.from(allAssumptions)
    val allAssertions = interpreter.getNonInternalAssertionNodes
    val assertions = UserLevelDependencyAnalysisNode.from(allAssertions)
    val nodes = UserLevelDependencyAnalysisNode.from(allAssertions.union(allAssumptions))
    println(s"#Assumptions = ${assumptions.size}")
    println(s"#Assertions = ${assertions.size}")
    println(s"#Nodes = ${nodes.size}")
    println(s"#low-level Assumptions (non-internal) = ${allAssumptions.size}")
    println(s"#low-level Assumptions (all) = ${interpreter.getAssumptionNodes.size}")
    println(s"#low-level Assertions (non-internal) = ${allAssertions.size}")
    println(s"#low-level Assertions (all) = ${interpreter.getAssertionNodes.size}")
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

    val ((optProgressPeter, optProgressLea, optInfo), optTime) = measureTime(fullGraphInterpreter.computeVerificationProgress())
    //    println(s"Overall verification progress: $progress")
    println(s"$optInfo")
    println(s"Peter: $optProgressPeter; Lea: $optProgressLea")
    println(s"Finished in ${optTime}ms")
  }

  private def handleVerificationProgressDEBUGQuery(): Unit = {

    println("\nNaive implementation")
    val ((naiveProgressPeter, naiveProgressLea, naiveInfo), naiveTime) = measureTime(fullGraphInterpreter.computeVerificationProgressNaive())
//    println(s"Overall verification progress: $progress")
    println(s"$naiveInfo")
    println(s"Peter: $naiveProgressPeter; Lea: $naiveProgressLea")
    println(s"Finished in ${naiveTime}ms")

    println("\nOptimized implementation")
    val ((optProgressPeter, optProgressLea, optInfo), optTime) = measureTime(fullGraphInterpreter.computeVerificationProgressOptimized())
    //    println(s"Overall verification progress: $progress")
    println(s"$optInfo")
    println(s"Peter: $optProgressPeter; Lea: $optProgressLea")
    println(s"Finished in ${optTime}ms")
    if(Math.abs(naiveProgressPeter - optProgressPeter) > 0.001 || Math.abs(naiveProgressLea - optProgressLea) > 0.001) println("Fail: Progress is not equal!")
    else println("Success: Progress is equal!")
  }

  private def handleVerificationProgressNaiveQuery(): Unit = {

    val ((naiveProgressPeter, naiveProgressLea, naiveInfo), naiveTime) = measureTime(fullGraphInterpreter.computeVerificationProgressNaive())
    //    println(s"Overall verification progress: $progress")
    println(s"$naiveInfo")
    println(s"Peter: $naiveProgressPeter; Lea: $naiveProgressLea")
    println(s"Finished in ${naiveTime}ms")
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

  private def handlePrecisionEval(inputs: Seq[String]): Unit = {
    val labelPattern: Regex = """@label\("([^"]+)"\)""".r
    val header = "Assertion Label,Sound?,#True Dependencies,#Reported Dependencies,#False-Positives,Runtime"

    def readFile(path: String): Map[String, List[String]] = {
      val src = Source.fromFile(path)
      try {
        src.getLines()
          .filter(_.trim.nonEmpty)        // skip empty lines
          .map { line =>
            val Array(left, right) = line.split("=", 2)  // split into key and rest
            val key = left.trim
            val values = right.split(",").map(_.trim).toList
            key -> values
          }
          .toMap
      } finally {
        src.close()
      }
    }

    def addOutput(bw: BufferedWriter, output: String): Unit = {
      bw.write(output)
      bw.newLine()
      println(output)
    }

    def evalSingleAssertion(assertionLabel: String, dependencyLabels: List[String], bw: BufferedWriter): Unit = {
      val startAnalysis = System.nanoTime()
      val queriedAssertions = fullGraphInterpreter.getAssertionNodesByLabel(assertionLabel)
      val allDependencies = fullGraphInterpreter.getAllNonInternalDependencies(queriedAssertions.map(_.id))
      val sourceDependencies = UserLevelDependencyAnalysisNode.from(allDependencies).getSourceSet().diff(UserLevelDependencyAnalysisNode.from(queriedAssertions).getSourceSet())

      val endAnalysis = System.nanoTime()
      val durationMs = (endAnalysis - startAnalysis) / 1e6

      val sourceDependenciesString = sourceDependencies.mkString("\n\t")

      val isSound = dependencyLabels.forall(sourceDependenciesString.contains)
      val imprecise = sourceDependencies.filter(node =>
        labelPattern.findFirstMatchIn(node.toString) match {
          case Some(label) => !dependencyLabels.contains(label.group(1))
          case _ => true
      })

      addOutput(bw, s"$assertionLabel,${if(isSound) "YES" else "NO"},${dependencyLabels.size},${sourceDependencies.size},${imprecise.size},${durationMs}ms")

//      println(s"Queried:\n\t${getSourceInfoString(queriedAssertions)}")
//      println(s"\nAll Dependencies (${timeAll}ms):\n\t$sourceDependenciesString")
//
//      if(queriedAssertions.exists(_.asInstanceOf[GeneralAssertionNode].hasFailed)) println("\nQueried assertions (partially) FAILED!\n")
    }

    assert(inputs.size == 1)
    val pathToGroundTruth = inputs.head

    val bw = new BufferedWriter(new FileWriter(pathToGroundTruth.replace(".txt", "_result.csv")))

    try {
      val groundTruths = readFile(pathToGroundTruth)
      addOutput(bw, header)
      groundTruths.foreach { case (assertionLabel, dependencyLabels) => evalSingleAssertion(assertionLabel, dependencyLabels, bw) }

      bw.close()
      println("Done.")
    }catch {
      case _ => println("Failed.")
    }finally {
      bw.close()
    }
  }

  private def handleAnnotateQuery(inputs: Seq[String]): Unit = {
    var n = 0
    def nextN: Int = {
      n = n + 1
      n
    }

    def newInfo(info: ast.Info): ast.Info = MakeInfoPair(AnnotationInfo(Map(("label", Seq(s"L$nextN")))), info)


    def annotateConjungts(exp: ast.Exp): ast.Exp = {
      exp match {
        case ast.And(l, r) => ast.And(annotateConjungts(l), annotateConjungts(r))(exp.pos, exp.info, exp.errT)
        case _ => annotateExp(exp)
      }
    }

    def annotateExp(exp: ast.Exp): ast.Exp = exp.withMeta((exp.pos, newInfo(exp.info), exp.errT))

    def annotateSeqn(seqn: ast.Seqn):ast.Seqn = Seqn(seqn.ss.map(annotateStmt), seqn.scopedSeqnDeclarations)(seqn.pos, seqn.info, seqn.errT)

    def annotateStmt(stmt: ast.Stmt): ast.Stmt = {
      stmt match {
        case Inhale(exp) => Inhale(annotateConjungts(exp))(exp.pos, exp.info, exp.errT)
        case Assume(exp) => Assume(annotateConjungts(exp))(exp.pos, exp.info, exp.errT)
        case seqn: Seqn => annotateSeqn(seqn)
        case If(cond, thn, els) => If(annotateExp(cond), annotateSeqn(thn), annotateSeqn(els))(stmt.pos, stmt.info, stmt.errT)
        case While(cond, invs, body) => While(annotateExp(cond), invs.map(annotateConjungts), annotateSeqn(body))(stmt.pos, stmt.info, stmt.errT)
        case Label(name, invs) => Label(name, invs.map(annotateConjungts))(stmt.pos, stmt.info, stmt.errT)
        case _: Goto | _: LocalVarDeclStmt => stmt
        case Package(wand, proofScript) => Package(wand, annotateSeqn(proofScript))(stmt.pos, newInfo(stmt.info), stmt.errT)
        case _ => stmt.withMeta((stmt.pos, newInfo(stmt.info), stmt.errT))
      }
    }

    def annotateDomain(domain: ast.Domain): ast.Domain = {
      def annotateAxiom(axiom: ast.DomainAxiom): ast.DomainAxiom = axiom match {
        case NamedDomainAxiom(name, exp) => NamedDomainAxiom(name, annotateExp(exp))(axiom.pos, axiom.info, axiom.domainName, axiom.errT)
        case AnonymousDomainAxiom(exp) => AnonymousDomainAxiom(annotateExp(exp))(axiom.pos, axiom.info, axiom.domainName, axiom.errT)
      }
      domain.copy(axioms = domain.axioms.map(annotateAxiom))(domain.pos, domain.info, domain.errT)
    }

    def annotateFunction(function: ast.Function): ast.Function =
      function.copy(pres=function.pres.map(annotateConjungts), posts=function.posts.map(annotateConjungts), body=function.body.map(annotateExp))(function.pos, function.info, function.errT)

    def annotateMethod(method: ast.Method): ast.Method =
      method.copy(pres=method.pres.map(annotateConjungts), posts=method.posts.map(annotateConjungts), body=method.body.map(annotateSeqn))(method.pos, method.info, method.errT)

    val newProgram: ast.Program = program.copy(domains=program.domains.map(annotateDomain), functions=program.functions.map(annotateFunction),
      methods=program.methods.map(annotateMethod))(program.pos, program.info, program.errT)

    val writer = new PrintWriter(inputs.head)
    writer.println(newProgram.toString())
    writer.close()
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

    val assumptionRanking = fullGraphInterpreter.computeAssumptionRanking().filter(_._2 > 0.0)
    println(s"Assumptions/unverified assertions and the number of dependents:\n\t${assumptionRanking.mkString("\n\t")}\n")

    println("Uncovered source code per method: ")
    val memberCoverageRanking = memberInterpreters.filter(mInterpreter => mInterpreter.getMember.isDefined && mInterpreter.getMember.get.isInstanceOf[Method])
      .map(mInterpreter => (mInterpreter.getMember.get.name, mInterpreter.computeUncoveredStatements()))
      .toList.filter(_._2 > 0).sortBy(_._2).reverse
    println(s"\nMethods and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n")
  }

  def handleVerificationGuidanceOldQuery(): Unit = {

    val assumptionRanking = fullGraphInterpreter.computeAssumptionRankingOld().filter(_._2 > 0)
    println(s"Assumptions and the number of dependents:\n\t${assumptionRanking.mkString("\n\t")}\n")

    val memberCoverageRanking = memberInterpreters.filter(mInterpreter => mInterpreter.getMember.isDefined && mInterpreter.getMember.get.isInstanceOf[Method])
      .map(mInterpreter => (mInterpreter.getMember.get.name, mInterpreter.computeUncoveredStatements()))
      .toList.filter(_._2 > 0).sortBy(_._2).reverse
    println(s"Methods and the number of uncovered statements:\n\t${memberCoverageRanking.mkString("\n\t")}\n")
  }
}
