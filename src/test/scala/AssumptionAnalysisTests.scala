
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis._
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.VerificationResult
import viper.silver.{ast, verifier}

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import scala.annotation.unused
import scala.jdk.CollectionConverters.IterableHasAsScala
import java.time._
import java.time.format.DateTimeFormatter


class AssumptionAnalysisTests extends AnyFunSuite {

  val CHECK_PRECISION = false
  val EXECUTE_PRECISION_BENCHMARK = false
  val EXECUTE_TEST=true
  val ignores: Seq[String] = Seq("example1", "example2", "graph-copy")
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/unitTests",
//    "dependencyAnalysisTests/real-world-examples",
//    "dependencyAnalysisTests/quick"
//    "dependencyAnalysisTests/fromSilver"
  )

  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"

  var commandLineArguments: Seq[String] =
    Seq("--timeout", "100" /* seconds */ , "--enableAssumptionAnalysis", "--z3Args", "proof=true unsat-core=true")


  if(EXECUTE_PRECISION_BENCHMARK) {
    test("precision benchmark") {
      val basePath = "src/test/resources/dependencyAnalysisTests/precisionTests/results"
      val directory = new File(basePath)
      directory.mkdir()
      val now: LocalDateTime = LocalDateTime.now()
      val formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")
      val writer = new PrintWriter(s"$basePath/result_${now.format(formatter)}.out")
      visitFiles("dependencyAnalysisTests/precisionTests", executePrecisionBenchmark(_, _, writer))
      writer.close()
    }
  }

//  createSingleTest("dependencyAnalysisTests/quick", "test")

  if(EXECUTE_TEST)
    testDirectories foreach (dir => visitFiles(dir, createSingleTest))

  commandLineArguments = Seq("--enableMoreCompleteExhale") ++ commandLineArguments
  if(EXECUTE_TEST)
    visitFiles("dependencyAnalysisTests/mce", createSingleTest)




  def visitFiles(dirName: String, function: (String, String) => Unit): Unit = {
    val path = Paths.get(getClass.getClassLoader.getResource(dirName).toURI)
    visitFiles(path, dirName, function)
  }

  private def createSingleTest(dirName: String, fileName: String): Unit = {
    test(dirName + "/" + fileName) {
      try{
        initFrontend()
        executeTest(dirName + "/", fileName, frontend)
      }catch{
        case t: Throwable => fail(t.getMessage)
      }
    }
  }

  def visitFiles(path: Path, dirName: String, function: (String, String) => Unit): Unit = {
    val directoryStream = Files.newDirectoryStream(path).asScala
    val dirContent = directoryStream.toList

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)) {
      if(Files.isDirectory(filePath)){
        visitFiles(filePath, dirName + "/" + filePath.getFileName.toString, function)
      }else{
        val rawFileName = filePath.getFileName.toString
        if (rawFileName.endsWith(".vpr")) {
          val fileName = rawFileName.replace(".vpr", "")
          if (!ignores.contains(fileName))
            function(dirName, fileName)
        }
      }
    }
  }

  var frontend: SiliconFrontend = createFrontend()

  def initFrontend(): Unit = {
    frontend.verifier.stop()
    frontend = createFrontend()
  }

  def createFrontend(): SiliconFrontend = {
    val reporter = DependencyAnalysisReporter()
    val fe = new SiliconFrontend(reporter)
    val backend = fe.createVerifier("")
    backend.parseCommandLine(commandLineArguments ++ List("--ignoreFile", "dummy.sil"))
    fe.init(backend)
    fe.setVerifier(backend)
    backend.start()
    fe
  }

  def executeTest(filePrefix: String,
                  fileName: String,
                  frontend: SilFrontend): Unit = {

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      cancel(f"Program does not verify. Skip test.\n$result")
      return
    }

    val assumptionAnalysisInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpreters

    new AnnotatedTest(program, assumptionAnalysisInterpreters).execute()
    PruningTest(filePrefix + "/" + fileName, program, AssumptionAnalysisInterpreter.joinGraphsAndGetInterpreter(Some(fileName), assumptionAnalysisInterpreters.toSet)).execute()
  }

  def executePrecisionBenchmark(filePrefix: String,
                                fileName: String,
                                writer: PrintWriter): Unit = {
    initFrontend()
    println(s"Precision Benchmark for $filePrefix - $fileName started...")
    try{
      val program: Program = tests.loadProgram(filePrefix + "/", fileName, frontend)
      val result = frontend.verifier.verify(program)
      if(result.isInstanceOf[verifier.Failure]) {
        writer.println("Program does not verify. Skip")
        println(f"Program does not verify. Skip.\n$result")
        return
      }
      val assumptionAnalysisInterpreters = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalysisInterpreters
      writer.println(s"$filePrefix - $fileName")
      val fullGraphInterpreter = AssumptionAnalysisInterpreter.joinGraphsAndGetInterpreter(Some(fileName), assumptionAnalysisInterpreters.toSet)
      new PrecisionBenchmarkSoundnessTest(filePrefix + "/" + fileName, program, fullGraphInterpreter, writer).execute()
      new AnnotatedPrecisionBenchmark(program, assumptionAnalysisInterpreters, writer).execute()
      writer.println()
      println(s"Precision Benchmark for $filePrefix - $fileName done.")
    }catch{
      case e: Exception =>
        writer.println("Failed. Skip")
        println(s"Exception caught: ${e.getMessage}")
    }
  }

  /**
   * (Almost) Fully automated test, which takes a program and its assumption analysis results and,
   * for each explicit assertion, builds a new program that only contains said assertion and
   * all its dependencies. The test passes if all new programs verify successfully.
   *
   * Statements that are only required as a trigger need to be manually annotated with @trigger() by the user.
   */
  case class PruningTest(fileName: String, program: Program, fullGraphInterpreter: AssumptionAnalysisInterpreter) {

    def execute(): Unit = {
      val triggerNodeLines = fullGraphInterpreter.getNodes.filter(node => node.sourceInfo.getTopLevelSource.toString.contains("@trigger()")).flatMap(_.sourceInfo.getLineNumber)
      var id: Int = 0
      // TODO ake: safer would be to work with position string instead of line numbers
      fullGraphInterpreter.getExplicitAssertionNodes flatMap (_.sourceInfo.getLineNumber) foreach {line =>
          pruneAndVerify(Set(line) ++ triggerNodeLines, "src/test/resources/" + fileName + s"_test$id.out")
          id += 1
        }
    }

    protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Unit = {
      val relevantNodes = relevantLines.flatMap(line => fullGraphInterpreter.getNodesByLine(line))

      val dependencies = fullGraphInterpreter.getAllNonInternalDependencies(relevantNodes.map(_.id))

      val crucialNodes = relevantNodes ++ dependencies
      val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes)
      val result = frontend.verifier.verify(newProgram)
      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      assert(!result.isInstanceOf[verifier.Failure], s"Failed to verify new program ${newProgram.toString()}")
    }

    protected def exportPrunedProgram(exportFileName: String, newProgram: Program, pruningFactor: Double, result: VerificationResult): Unit = {
      val writer = new PrintWriter(exportFileName)
      writer.println("// test result: " + !result.isInstanceOf[verifier.Failure])
      writer.println("// cleanse factor: " + pruningFactor)
      writer.println(newProgram.toString())
      writer.close()
    }

    protected def getPrunedProgram(crucialNodes: Set[AssumptionAnalysisNode]): (ast.Program, Double) = {
      val crucialNodeSourceInfos = crucialNodes map (_.sourceInfo.getTopLevelSource)
      var total = 0
      var removed = 0
      var nonDetermBoolCount = 0

      def getNextNonDetermBool: String = {
        nonDetermBoolCount += 1
        s"nonDetermBool_$nonDetermBoolCount"
      }

      val newProgram: ast.Program = ViperStrategy.Slim({
        case s @(_: ast.Seqn | _: ast.Goto) => s
        case meth@ast.Method(name, inVars, outVars, pres, posts, body) =>
          val newPres = pres filter (isCrucialExp(_, crucialNodeSourceInfos))
          val newPosts = posts filter (isCrucialExp(_, crucialNodeSourceInfos))
          total += pres.size + posts.size
          removed += (pres.size - newPres.size) + (posts.size - newPosts.size)
          ast.Method(name, inVars, outVars, newPres, newPosts, body)(meth.pos, meth.info, meth.errT)
        case ifStmt@ast.If(cond, thenBody, elseBody) if !isCrucialExp(cond, crucialNodeSourceInfos) =>
          total += 1
          removed += 1
          val nonDetermBool = getNextNonDetermBool
          ast.Seqn(Seq(
            ast.LocalVarDeclStmt(ast.LocalVarDecl(nonDetermBool, ast.Bool)())(),
            ast.If(ast.LocalVar(nonDetermBool, ast.Bool)(), thenBody, elseBody)())
            , Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
        case ifStmt: If =>
          total += 1
          ifStmt
        case whileStmt@ast.While(cond, invs, body) if !isCrucialExp(cond, crucialNodeSourceInfos) =>
          val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
          total += 1 + invs.size
          removed += 1 + (invs.size - newInvs.size)
          val nonDetermBool = getNextNonDetermBool
          ast.Seqn(Seq(
            ast.LocalVarDeclStmt(ast.LocalVarDecl(nonDetermBool, ast.Bool)())(),
            ast.While(ast.LocalVar(nonDetermBool, ast.Bool)(), newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT))
            , Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
        case whileStmt@ast.While(cond, invs, body) =>
          val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
          total += 1 + invs.size
          removed += (invs.size - newInvs.size)
          ast.While(cond, newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT)
        case label@ast.Label(name, invs) =>
          val newInvs = invs filter (isCrucialExp(_, crucialNodeSourceInfos))
          total += 1 + invs.size
          removed += (invs.size - newInvs.size)
          ast.Label(name, newInvs)(label.pos, label.info, label.errT)
        case s: ast.Package if !isCrucialStmt(s, crucialNodeSourceInfos) =>
          total += 1
          removed += 1
          ast.Inhale(ast.TrueLit()())()
        case s: Stmt if !isCrucialStmt(s, crucialNodeSourceInfos) =>
          total += 1
          removed += 1
          ast.Inhale(ast.TrueLit()())()
        case s: Stmt =>
          total += 1
          s
      }, Traverse.BottomUp).execute(program)
      (newProgram, removed.toDouble / total.toDouble)
    }

    protected def isCrucialExp(exp: ast.Exp, crucialNodesWithExpInfo: Set[AnalysisSourceInfo]): Boolean = {
      crucialNodesWithExpInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(exp.pos))) // TODO ake: currently we compare only lines not columns!
    }

    protected def isCrucialStmt(stmt: ast.Stmt, crucialNodesWithStmtInfo: Set[AnalysisSourceInfo]): Boolean = {
      crucialNodesWithStmtInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(stmt.pos)))
    }
  }

  /**
   * Takes a Viper program and its assumption analysis results and checks whether the analysis found the
   * assumptions, assertions and dependencies between them, as annotated by the user.
   *
   * Annotations
   * @dependency() -> for assumptions that should be reported as a dependency
   * @irrelevant() -> for assumptions that should NOT be reported as a dependency
   * @testAssertion() -> the queried assertion
   *
   * !!! THERE CAN ONLY BE 1 TEST ASSERTION PER METHOD,
   * but multiple dependency/irrelevant annotations are allowed
   *
   */
  class AnnotatedTest(program: Program, assumptionAnalysisInterpreters: List[AssumptionAnalysisInterpreter]) {
    def execute(): Unit = {
      val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedStmts({ annotationInfo => annotationInfo.values.contains(irrelevantKeyword) || annotationInfo.values.contains(dependencyKeyword) })
      val allAssumptionNodes = assumptionAnalysisInterpreters.flatMap(_.getNonInternalAssumptionNodes)

      var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
      errorMsgs ++= assumptionAnalysisInterpreters flatMap checkTestAssertionNodeExists
      errorMsgs ++= assumptionAnalysisInterpreters flatMap checkDependencies
      val warnMsgs = assumptionAnalysisInterpreters flatMap checkNonDependencies
      if (CHECK_PRECISION)
        errorMsgs ++= warnMsgs
      else if (warnMsgs.nonEmpty) println(warnMsgs.mkString("\n")) // TODO ake: should be a warning

      val check = errorMsgs.isEmpty
      assert(check, "\n" + errorMsgs.mkString("\n"))
    }

    protected def extractAnnotatedStmts(annotationFilter: (ast.AnnotationInfo => Boolean)): Set[ast.Infoed] = {
      var nodesWithAnnotation: Set[ast.Infoed] = Set.empty
      @unused
      val newP: ast.Program = ViperStrategy.Slim({
        case s: ast.Seqn => s
        case n: ast.Infoed =>
          val annotationInfo = n.info.getUniqueInfo[ast.AnnotationInfo]
            .filter(annotationFilter)
          if (annotationInfo.isDefined)
            nodesWithAnnotation += n
          n
      }).execute(program)
      nodesWithAnnotation
    }

    protected def checkAssumptionNodeExists(analysisNodes: List[AssumptionAnalysisNode], node: ast.Infoed): Option[String] = {
      val pos = extractSourceLine(node.asInstanceOf[ast.Positioned].pos)
      val annotationInfo = node.info.getUniqueInfo[ast.AnnotationInfo]
        .map(ai => ai.values.getOrElse(irrelevantKeyword, ai.values.getOrElse(dependencyKeyword, List.empty))).getOrElse(List.empty)
      val assumptionType = annotationInfo.map(AssumptionType.fromString).filter(_.isDefined).map(_.get)
      val nodeExists = analysisNodes exists (analysisNode => {
          extractSourceLine(analysisNode.sourceInfo.getPosition) == pos &&
          assumptionType.forall(_.equals(analysisNode.assumptionType))
      })
      Option.when(!nodeExists)(s"Missing analysis node:\n${node.toString}\n$pos")
    }

    protected def extractSourceLine(pos: ast.Position): Int = {
      pos match {
        case column: ast.HasLineColumn => column.line
        case _ => -1
      }
    }

    protected def checkTestAssertionNodeExists(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assumptionNodes = getTestAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes) ++ getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)
      if (assumptionNodes.nonEmpty && assertionNodes.isEmpty)
        Seq(s"Missing testAssertion for member: ${assumptionAnalysisInterpreter.getName}")
      else
        Seq.empty
    }


    protected def checkDependencies(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assumptionNodes = getTestAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)

      val dependenciesTmp = assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))
      val dependencies = dependenciesTmp.map(_.id)

      assumptionsPerSource.map({ case (_, assumptions) =>
        val hasDependency = dependencies.intersect(assumptions.map(_.id)).nonEmpty
        Option.when(!hasDependency)(s"Missing dependency: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
    }

    protected def checkNonDependencies(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Seq[String] = {
      val assumptionNodes = getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)

      val dependencies = assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id)).map(_.id)

      assumptionsPerSource.map({ case (_, assumptions) =>
        val hasDependency = dependencies.intersect(assumptions.map(_.id)).nonEmpty
        Option.when(hasDependency)(s"Unexpected dependency: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
    }

    protected def getTestAssertionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(node => node.sourceInfo.toString.contains("@" + testAssertionKeyword + "("))


    protected def getTestAssumptionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + dependencyKeyword + "("))


    protected def getTestIrrelevantAssumptionNodes(nodes: Set[AssumptionAnalysisNode]): Set[AssumptionAnalysisNode] =
      nodes.filter(_.sourceInfo.toString.contains("@" + irrelevantKeyword + "("))

  }


  class AnnotatedPrecisionBenchmark(program: Program, assumptionAnalysisInterpreters: List[AssumptionAnalysisInterpreter],
                                    writer: PrintWriter) extends AnnotatedTest(program, assumptionAnalysisInterpreters) {
    override def execute(): Unit = {

      assumptionAnalysisInterpreters foreach {a =>
        val prec = computePrecision(a)
        writer.println(s"${a.getMember.map(_.name).getOrElse("unknown")}: $prec")
      }
    }

    protected def computePrecision(assumptionAnalysisInterpreter: AssumptionAnalysisInterpreter): Double = {
      val assumptionNodes = getTestIrrelevantAssumptionNodes(assumptionAnalysisInterpreter.getNonInternalAssumptionNodes)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = getTestAssertionNodes(assumptionAnalysisInterpreter.getNonInternalAssertionNodes)

      val dependencies = assumptionAnalysisInterpreter.getAllNonInternalDependencies(assertionNodes.map(_.id))
      val dependenciesPerSource = dependencies groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val dependencyIds = dependencies.map(_.id)

      if(dependenciesPerSource.nonEmpty){
        val wrongDependencies = assumptionsPerSource.filter({ case (_, assumptions) => dependencyIds.intersect(assumptions.map(_.id)).nonEmpty })
        1.0 - (wrongDependencies.size.toDouble / dependenciesPerSource.size.toDouble) // TODO ake: or / assumptionsPerSource.size.toDouble?
      }else{
        1.0
      }
    }

  }


  class PrecisionBenchmarkSoundnessTest(name: String, program: Program, fullGraphInterpreter: AssumptionAnalysisInterpreter ,
                                        writer: PrintWriter) extends PruningTest(name, program, fullGraphInterpreter) {

    override def execute(): Unit = {
      val irrelevantNodes = fullGraphInterpreter.getNodes.filter(node => node.sourceInfo.toString.contains("@irrelevant(")).flatMap(_.sourceInfo.getLineNumber)

      val relevantLines = fullGraphInterpreter.getNodes.flatMap(_.sourceInfo.getLineNumber).diff(irrelevantNodes)

      pruneAndVerify(relevantLines, "src/test/resources/" + fileName + s"_test.out")
    }

    override protected def pruneAndVerify(relevantLines: Set[Int], exportFileName: String): Unit = {
      val relevantNodes = relevantLines.flatMap(line => fullGraphInterpreter.getNodesByLine(line))

      val crucialNodes = relevantNodes
      val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes)
      val result = frontend.verifier.verify(newProgram)
      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      if(result.isInstanceOf[verifier.Failure]) {
        writer.println(s"!!!!!!!!!!!\nFailed to verify new program $exportFileName\n")
        println(s"!!!!!!!!!!!\nFailed to verify new program $exportFileName\n")
        throw new Exception("Error: " + result.toString)
      }
    }

  }
}


