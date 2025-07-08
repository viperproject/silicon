
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.VerificationResult
import viper.silver.{ast, verifier}

import java.io.PrintWriter
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.IterableHasAsScala


class AssumptionAnalysisTests extends AnyFunSuite {

  val CHECK_PRECISION = false
  val ignores: Seq[String] = Seq()
  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests",
//    "dependencyAnalysisTests/quick",
    "examples/binary-search",
    //      "examples/graph-copy",
    //      "examples/graph-marking",
    "examples/max_array",
    "examples/quickselect",
//    "examples/longest-common-prefix",
//    "examples/tree-delete-min",
  )

  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"

  val commandLineArguments: Seq[String] =
    Seq("--timeout", "100" /* seconds */ , "--enableAssumptionAnalysis", "--z3Args", "proof=true unsat-core=true")

  testDirectories foreach createTests

  //  test("dependencyAnalysisTests/all" + "/" + "misc"){
  //    executeTest("examples/max_array/", "max-array-standard", frontend)
  //  }

  def createTests(dirName: String): Unit = {
    val path = Paths.get(getClass.getClassLoader.getResource(dirName).toURI)
    createTests(path, dirName)
  }

  def createTests(path: Path, dirName: String): Unit = {
    val directoryStream = Files.newDirectoryStream(path).asScala
    val dirContent = directoryStream.toList

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)) {
      if(Files.isDirectory(filePath)){
        createTests(filePath, dirName + "/" + filePath.getFileName.toString)
      }else{
        val rawFileName = filePath.getFileName.toString
        if (rawFileName.endsWith(".vpr")) {
          val fileName = rawFileName.replace(".vpr", "")
          if (!ignores.contains(fileName))
            test(dirName + "/" + fileName) {
              executeTest(dirName + "/", fileName, frontend)
            }
        }
      }
    }
  }

  def frontend: SiliconFrontend = {
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
    if (result.isInstanceOf[verifier.Failure]) {
      println("Program does not verify. Skip test.")
      return
    }

    val assumptionAnalyzers = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalyzers

    PruningTest(filePrefix + "/" + fileName, program, assumptionAnalyzers).execute()

    AnnotatedTest(program, assumptionAnalyzers).execute()
  }

  /**
   * (Almost) Fully automated test, which takes a program and its assumption analysis results and,
   * for each explicit assertion, builds a new program that only contains said assertion and
   * all its dependencies. The test passes if all new programs verify successfully.
   *
   * Statements that are only required as a trigger need to be manually annotated with @trigger() by the user.
   */
  case class PruningTest(fileName: String, program: Program, assumptionAnalyzers: List[AssumptionAnalyzer]) {
    private val fullGraph: AssumptionAnalysisGraph = AssumptionAnalyzer.joinGraphs(assumptionAnalyzers.map(_.assumptionGraph).toSet)

    def execute(): Unit = {
      val triggerNodes = fullGraph.nodes.filter(node => node.sourceInfo.getTopLevelSource.toString.contains("@trigger()"))
      var id: Int = 0
      fullGraph.getExplicitAssertionNodes.groupBy(_.sourceInfo.getPositionString).foreach { case (_, nodes) =>
          pruneAndVerify(nodes ++ triggerNodes, "src/test/resources/" + fileName + s"_test$id.out")
          id += 1
        }
    }

    private def pruneAndVerify(nodesToAnalyze: Set[AssumptionAnalysisNode], exportFileName: String): Unit = {
      val sourcePositionsToAnalyze = nodesToAnalyze map (_.sourceInfo.getPositionString)
      val explicitAssertionNodeIds = fullGraph.nodes.filter(n => sourcePositionsToAnalyze.contains(n.sourceInfo.getPositionString)).map(_.id).toSet

      val dependencies = fullGraph.getAllNonInternalDependencies(explicitAssertionNodeIds)

      val crucialNodes = nodesToAnalyze ++ dependencies
      val (newProgram, pruningFactor) = getPrunedProgram(crucialNodes)
      val result = frontend.verifier.verify(newProgram)
      exportPrunedProgram(exportFileName, newProgram, pruningFactor, result)
      assert(!result.isInstanceOf[verifier.Failure], s"Failed to verify new program ${newProgram.toString()}")
    }

    private def exportPrunedProgram(exportFileName: String, newProgram: Program, pruningFactor: Double, result: VerificationResult): Unit = {
      val writer = new PrintWriter(exportFileName)
      writer.println("// test result: " + !result.isInstanceOf[verifier.Failure])
      writer.println("// cleanse factor: " + pruningFactor)
      writer.println(newProgram.toString())
      writer.close()
    }

    private def getPrunedProgram(crucialNodes: Set[AssumptionAnalysisNode]): (ast.Program, Double) = {
      val crucialNodesWithStmtInfo = crucialNodes filter (_.sourceInfo.getTopLevelSource.isInstanceOf[StmtAnalysisSourceInfo]) map (_.sourceInfo.getTopLevelSource.asInstanceOf[StmtAnalysisSourceInfo])
      val crucialNodesWithExpInfo = crucialNodes filter (_.sourceInfo.getTopLevelSource.isInstanceOf[ExpAnalysisSourceInfo]) map (_.sourceInfo.getTopLevelSource.asInstanceOf[ExpAnalysisSourceInfo])
      var total = 0
      var removed = 0

      val newProgram: Program = ViperStrategy.Slim({
        case s: Seqn => s
        case meth@ast.Method(name, inVars, outVars, pres, posts, body) =>
          val newPres = pres filter (isCrucialExp(_, crucialNodesWithExpInfo))
          val newPosts = posts filter (isCrucialExp(_, crucialNodesWithExpInfo))
          total += pres.size + posts.size
          removed += (pres.size - newPres.size) + (posts.size - newPosts.size)
          ast.Method(name, inVars, outVars, newPres, newPosts, body)(meth.pos, meth.info, meth.errT)
        case ifStmt@ast.If(cond, thenBody, elseBody) if !isCrucialExp(cond, crucialNodesWithExpInfo) =>
          total += 1
          removed += 1
          ast.Seqn(Seq(
            ast.LocalVarDeclStmt(ast.LocalVarDecl("nonDetermBool", ast.Bool)())(),
            ast.If(ast.LocalVar("nonDetermBool", ast.Bool)(), thenBody, elseBody)())
            , Seq())(ifStmt.pos, ifStmt.info, ifStmt.errT)
        case ifStmt: If =>
          total += 1
          ifStmt
        case whileStmt@ast.While(cond, invs, body) if !isCrucialExp(cond, crucialNodesWithExpInfo) =>
          val newInvs = invs filter (isCrucialExp(_, crucialNodesWithExpInfo))
          total += 1 + invs.size
          removed += 1 + (invs.size - newInvs.size)
          ast.Seqn(Seq(
            ast.LocalVarDeclStmt(ast.LocalVarDecl("nonDetermBool", ast.Bool)())(),
            ast.While(ast.LocalVar("nonDetermBool", ast.Bool)(), newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT))
            , Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
        case whileStmt@ast.While(cond, invs, body) =>
          val newInvs = invs filter (isCrucialExp(_, crucialNodesWithExpInfo))
          total += 1 + invs.size
          removed += (invs.size - newInvs.size)
          ast.While(cond, newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT)
        case s: Stmt if !isCrucialStmt(s, crucialNodesWithStmtInfo) =>
          total += 1
          removed += 1
          ast.Inhale(ast.TrueLit()())()
        case s: Stmt =>
          total += 1
          s
      }, Traverse.BottomUp).execute(program)
      (newProgram, removed.toDouble / total.toDouble)
    }

    private def isCrucialExp(exp: ast.Exp, crucialNodesWithExpInfo: Set[ExpAnalysisSourceInfo]): Boolean = {
      crucialNodesWithExpInfo exists (n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(exp.pos))) // TODO ake: currently we compare only lines not columns!
    }

    private def isCrucialStmt(stmt: ast.Stmt, crucialNodesWithStmtInfo: Set[StmtAnalysisSourceInfo]): Boolean = {
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
  case class AnnotatedTest(program: Program, assumptionAnalyzers: List[AssumptionAnalyzer]) {
    def execute(): Unit = {
      val assumptionGraphs = assumptionAnalyzers map (_.assumptionGraph)
      val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedStmts({ annotationInfo => annotationInfo.values.contains(irrelevantKeyword) || annotationInfo.values.contains(dependencyKeyword) })
      val allAssumptionNodes = assumptionGraphs.flatMap(_.nodes.filter(_.isInstanceOf[GeneralAssumptionNode]))

      var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
      errorMsgs ++= assumptionAnalyzers flatMap checkTestAssertionNodeExists
      errorMsgs ++= assumptionGraphs flatMap checkDependencies
      val warnMsgs = assumptionGraphs flatMap checkNonDependencies
      if (CHECK_PRECISION)
        errorMsgs ++= warnMsgs
      else if (warnMsgs.nonEmpty) println(warnMsgs.mkString("\n")) // TODO ake: warning

      val check = errorMsgs.isEmpty
      assert(check, "\n" + errorMsgs.mkString("\n"))
    }

    private def extractAnnotatedStmts(annotationFilter: (ast.AnnotationInfo => Boolean)): Set[ast.Infoed] = {
      var nodesWithAnnotation: Set[ast.Infoed] = Set.empty
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

    private def checkAssumptionNodeExists(analysisNodes: List[AssumptionAnalysisNode], node: ast.Infoed): Option[String] = {
      val pos = extractSourceLine(node.asInstanceOf[ast.Positioned].pos)
      val annotationInfo = node.info.getUniqueInfo[ast.AnnotationInfo]
        .map(ai => ai.values.getOrElse(irrelevantKeyword, ai.values.getOrElse(dependencyKeyword, List.empty))).getOrElse(List.empty)
      val assumptionType = annotationInfo.map(AssumptionType.fromString).filter(_.isDefined).map(_.get)
      val nodeExists = analysisNodes exists (analysisNode => {
        analysisNode.isInstanceOf[GeneralAssumptionNode] &&
          !analysisNode.asInstanceOf[GeneralAssumptionNode].assumptionType.equals(AssumptionType.Internal) &&
          extractSourceLine(analysisNode.sourceInfo.getPosition) == pos &&
          assumptionType.forall(_.equals(analysisNode.assumptionType))
      })
      Option.when(!nodeExists)(s"Missing analysis node:\n${node.toString}\n$pos")
    }

    private def extractSourceLine(pos: ast.Position): Int = {
      pos match {
        case column: ast.HasLineColumn => column.line
        case _ => -1
      }
    }

    private def checkTestAssertionNodeExists(assumptionAnalyzer: AssumptionAnalyzer): Seq[String] = {
      val assumptionNodes = extractTestAssumptionNodesFromGraph(assumptionAnalyzer.assumptionGraph) ++ extractTestIrrelevantAssumptionNodesFromGraph(assumptionAnalyzer.assumptionGraph)
      val assertionNodes = extractTestAssertionNodesFromGraph(assumptionAnalyzer.assumptionGraph)
      if (assumptionNodes.nonEmpty && assertionNodes.isEmpty)
        Seq(s"Missing testAssertion for member: ${assumptionAnalyzer.getMember.map(_.name).getOrElse("unknown")}")
      else
        Seq.empty
    }

    private def checkDependencies(assumptionGraph: AssumptionAnalysisGraph): Seq[String] = {
      val assumptionNodes = extractTestAssumptionNodesFromGraph(assumptionGraph)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)

      assumptionsPerSource.map({ case (_, assumptions) =>
        val hasDeps = checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
        Option.when(!hasDeps)(s"Missing dependency: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
    }

    private def checkNonDependencies(assumptionGraph: AssumptionAnalysisGraph): Seq[String] = {
      val assumptionNodes = extractTestIrrelevantAssumptionNodesFromGraph(assumptionGraph)
      val assumptionsPerSource = assumptionNodes groupBy (n => extractSourceLine(n.sourceInfo.getPosition))
      val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)

      assumptionsPerSource.map({ case (_, assumptions) =>
        val hasDependency = checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
        Option.when(hasDependency)(s"Unexpected dependency: ${assumptions.head.sourceInfo.toString}")
      }).filter(_.isDefined).map(_.get).toSeq
    }

    private def checkDependenciesForSingleSource(assumptionGraph: AssumptionAnalysisGraph, assumptions: Seq[AssumptionAnalysisNode], assertions: Seq[AssumptionAnalysisNode]): Boolean = {
      assumptions exists (assumption => {
        assertions exists (assertion => assumptionGraph.existsAnyDependency(Set(assumption.id), Set(assertion.id)))
      })
    }

    private def extractTestAssertionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
      graph.nodes.filter(node =>
        (node.getNodeType.equals("Assertion") || node.getNodeType.equals("Exhale") || node.getNodeType.equals("Check")) &&
          node.sourceInfo.toString.contains("@" + testAssertionKeyword + "()")
      ).toSeq
    }

    private def extractTestAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
      graph.nodes.filter(node => {
        (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale") || node.getNodeType.equals("Infeasible")) &&
          !node.assumptionType.equals(AssumptionType.Internal) &&
          node.sourceInfo.toString.contains("@" + dependencyKeyword + "()")
      }
      ).toSeq
    }

    private def extractTestIrrelevantAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
      graph.nodes.filter(node => {
        (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale") || node.getNodeType.equals("Infeasible")) &&
          !node.assumptionType.equals(AssumptionType.Internal) &&
          node.sourceInfo.toString.contains("@" + irrelevantKeyword + "()")
      }
      ).toSeq
    }
  }
}
