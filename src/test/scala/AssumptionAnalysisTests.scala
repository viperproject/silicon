
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis._
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.{DiskLoader, ViperStrategy}
import viper.silver.ast.{If, Program, Seqn, Stmt}
import viper.silver.frontend.SilFrontend
import viper.silver.{ast, verifier}

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.IterableHasAsScala
import scala.util.{Failure, Success}


/**
 * Annotations
 * @dependency() -> for assumptions that should be reported as a dependency
 * @irrelevant() -> for assumptions that should NOT be reported as a dependency
 * @testAssertion() -> the queried assertion
 *
 * assumptions/assertions that are not annotated are ignored
 *
 * !!! THERE CAN ONLY BE 1 TEST ASSERTION PER METHOD,
 * but multiple dependency/irrelevant annotations are allowed
 *
 */
class AssumptionAnalysisTests extends AnyFunSuite {

  val CHECK_PRECISION = false
  val ignores: Seq[String] = Seq("infeasible")

  val irrelevantKeyword = "irrelevant"
  val dependencyKeyword = "dependency"
  val testAssertionKeyword = "testAssertion"

  val GENERATE_TESTS = false
  if(GENERATE_TESTS)
    generateTests("dependencyAnalysisTests/", "test-templates")


  val commandLineArguments: Seq[String] =
    Seq("--timeout", "100" /* seconds */, "--enableAssumptionAnalysis", "--z3Args", "proof=true unsat-core=true")


  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/unitTests",
    "dependencyAnalysisTests/all",
    "dependencyAnalysisTests/quick",
      "examples/binary-search",
//      "examples/graph-copy",
//      "examples/graph-marking",
      "examples/max_array",
      "examples/quickselect",
      "examples/longest-common-prefix",
      "examples/tree-delete-min",
  )
  testDirectories foreach createTests

//  test("dependencyAnalysisTests/all" + "/" + "misc"){
//    executeTest("examples/max_array/", "max-array-standard", frontend)
//  }


  def createTests(dirName: String): Unit = {
    val path = getClass.getClassLoader.getResource(dirName)
    val directoryStream = Files.newDirectoryStream(Paths.get(path.toURI)).asScala
    val dirContent = directoryStream.toList

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)
         if !Files.isDirectory(filePath)){
      val rawFileName = filePath.getFileName.toString
      if(rawFileName.endsWith(".vpr")){
        val fileName = rawFileName.replace(".vpr", "")
        if(!ignores.contains(fileName))
          test(dirName + "/" + fileName){
            executeTest(dirName + "/", fileName, frontend)
          }
      }
    }
  }

  def generateTests(filePrefix: String,
                    fileName: String): Unit = {
    val path = getClass.getClassLoader.getResource(filePrefix + fileName + ".vpr")
    val content: String = DiskLoader.loadContent(Paths.get(path.toURI)) match {
      case Failure(exception) => throw exception
      case Success(value) => value
    }

    val jsonPath = getClass.getClassLoader.getResource(filePrefix + "snippets" + ".json")
    val jsonContent: String = DiskLoader.loadContent(Paths.get(jsonPath.toURI)) match {
      case Failure(exception) => throw exception
      case Success(value) => value
    }
    val json = upickle.default.read[Map[String, Map[String, String]]](jsonContent)

    json foreach{case (testname, replacements) => generateSingleTestFile(filePrefix, fileName + "_" + testname, content, replacements)}
  }

  def generateSingleTestFile(filePrefix: String, fileName: String, template: String, replacements: Map[String, String]): Unit = {
    var newString = template
    val initPlaceholder = "##INIT##"
    val assumptionPlaceholder = "##ASSUMPTIONS##"
    val bodyPlaceholder = "##BODY##"
    val assertionPlaceholder = "##ASSERTION##"

    newString = newString.replaceAll(initPlaceholder, replacements("initString"))
    newString = newString.replaceAll(assumptionPlaceholder, replacements("assumptionString"))
    newString = newString.replaceAll(bodyPlaceholder, replacements("bodyString"))
    newString = newString.replaceAll(assertionPlaceholder, replacements("assertionString"))

    // write generated file
    val path2 = Paths.get("src/test/resources/" + filePrefix + fileName + "_generated" + ".vpr").toString
    val pw = new java.io.PrintWriter(new File(path2))
    try pw.write(newString) finally pw.close()
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
                  frontend: SilFrontend)
  : Unit = {

    val program: ast.Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)
    if(result.isInstanceOf[verifier.Failure]) {
      println("Program does not verify. Skip test.")
      return
    }

    val assumptionAnalyzers = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionAnalyzers

    val fullGraph = AssumptionAnalyzer.joinGraphs(assumptionAnalyzers.map(_.assumptionGraph).toSet)
    val triggerNodes = fullGraph.nodes.filter(node => node.sourceInfo.getTopLevelSource.toString.contains("@trigger()"))
    var id: Int = 0
    assumptionAnalyzers foreach (aa => {
      val explicitAssertionNodes = aa.assumptionGraph.getExplicitAssertionNodes.groupBy(_.sourceInfo.getPositionString)

      explicitAssertionNodes.foreach{case (_, nodes) =>
        removeNonDependenciesAndVerify(program, nodes ++ triggerNodes, fullGraph, "src/test/resources/" + filePrefix + fileName + s"_test$id.out")
        id += 1
      }
    })

    val assumptionGraphs = assumptionAnalyzers map (_.assumptionGraph)
    val stmtsWithAssumptionAnnotation: Set[ast.Infoed] = extractAnnotatedStmts(program, { annotationInfo => annotationInfo.values.contains(irrelevantKeyword) || annotationInfo.values.contains(dependencyKeyword)})
    val allAssumptionNodes = assumptionGraphs.flatMap(_.nodes.filter(_.isInstanceOf[GeneralAssumptionNode]))

    var errorMsgs = stmtsWithAssumptionAnnotation.map(checkAssumptionNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
    errorMsgs ++= assumptionAnalyzers flatMap checkTestAssertionNodeExists
    errorMsgs ++= assumptionGraphs flatMap checkDependencies
    val warnMsgs = assumptionGraphs flatMap checkNonDependencies
    if(CHECK_PRECISION)
      errorMsgs ++= warnMsgs
    else if(warnMsgs.nonEmpty) println(warnMsgs.mkString("\n")) // TODO ake: warning

    val check = errorMsgs.isEmpty
    assert(check, "\n" + errorMsgs.mkString("\n"))
  }

  private def extractAnnotatedStmts(program: ast.Program, annotationFiler: (ast.AnnotationInfo => Boolean)): Set[ast.Infoed] = {
    var nodesWithAnnotation: Set[ast.Infoed] = Set.empty
    val newP: ast.Program = ViperStrategy.Slim({
      case s: ast.Seqn => s
      case n: ast.Infoed =>
        val annotationInfo = n.info.getUniqueInfo[ast.AnnotationInfo]
          .filter(annotationFiler)
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

  def extractSourceLine(pos: ast.Position): Int = {
    pos match {
      case column: ast.HasLineColumn => column.line
      case _ => -1
    }
  }

  private def checkTestAssertionNodeExists(assumptionAnalyzer: AssumptionAnalyzer): Seq[String] = {
    val assumptionNodes = extractTestAssumptionNodesFromGraph(assumptionAnalyzer.assumptionGraph) ++ extractTestIrrelevantAssumptionNodesFromGraph(assumptionAnalyzer.assumptionGraph)
    val assertionNodes = extractTestAssertionNodesFromGraph(assumptionAnalyzer.assumptionGraph)
    if(assumptionNodes.nonEmpty && assertionNodes.isEmpty)
      Seq(s"Missing testAssertion for member: ${assumptionAnalyzer.getMember.map(_.name).getOrElse("unknown")}")
    else
      Seq.empty
  }

  def checkDependencies(assumptionGraph: AssumptionAnalysisGraph): Seq[String] = {
    val assumptionNodes = extractTestAssumptionNodesFromGraph(assumptionGraph)
    val assumptionsPerSource = assumptionNodes groupBy(n => extractSourceLine(n.sourceInfo.getPosition))
    val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)

    assumptionsPerSource.map({ case (_, assumptions) =>
      val hasDeps = checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
      Option.when(!hasDeps)(s"Missing dependency: ${assumptions.head.sourceInfo.toString}")
    }).filter(_.isDefined).map(_.get).toSeq
  }

  def checkNonDependencies(assumptionGraph: AssumptionAnalysisGraph): Seq[String] = {
    val assumptionNodes = extractTestIrrelevantAssumptionNodesFromGraph(assumptionGraph)
    val assumptionsPerSource = assumptionNodes groupBy(n => extractSourceLine(n.sourceInfo.getPosition))
    val assertionNodes = extractTestAssertionNodesFromGraph(assumptionGraph)

    assumptionsPerSource.map({case (_, assumptions) =>
      val hasDependency = checkDependenciesForSingleSource(assumptionGraph, assumptions, assertionNodes)
      Option.when(hasDependency)(s"Unexpected dependency: ${assumptions.head.sourceInfo.toString}")
    }).filter(_.isDefined).map(_.get).toSeq
  }

  def checkDependenciesForSingleSource(assumptionGraph: AssumptionAnalysisGraph, assumptions:  Seq[AssumptionAnalysisNode], assertions:  Seq[AssumptionAnalysisNode]): Boolean = {
    assumptions exists  (assumption => {
      assertions exists (assertion => assumptionGraph.existsAnyDependency(Set(assumption.id), Set(assertion.id)))
    })
  }

  def extractTestAssertionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node =>
      (node.getNodeType.equals("Assertion") || node.getNodeType.equals("Exhale") || node.getNodeType.equals("Check")) &&
        node.sourceInfo.toString.contains("@" + testAssertionKeyword + "()")
    ).toSeq
  }

  def extractTestAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node => {
      (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale")) &&
        !node.assumptionType.equals(AssumptionType.Internal) &&
        node.sourceInfo.toString.contains("@" + dependencyKeyword + "()")
    }
    ).toSeq
  }

  def extractTestIrrelevantAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node => {
      (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale")) &&
        !node.assumptionType.equals(AssumptionType.Internal) &&
        node.sourceInfo.toString.contains("@" + irrelevantKeyword + "()")
    }
    ).toSeq
  }

  def removeNonDependenciesAndVerify(program: ast.Program, nodesToAnalyze: Set[AssumptionAnalysisNode], fullGraph: AssumptionAnalysisGraph, exportFileName: String): Unit = {
    val sourcePositionsToAnalyze = nodesToAnalyze map (_.sourceInfo.getPositionString)
    val explicitAssertionNodeIds = fullGraph.nodes.filter(n => sourcePositionsToAnalyze.contains(n.sourceInfo.getPositionString)).map(_.id).toSet

    val dependencies = fullGraph.nodes filter (node =>
      ((node.isInstanceOf[GeneralAssumptionNode] && !node.assumptionType.equals(AssumptionType.Internal)) ||
        (node.isInstanceOf[GeneralAssertionNode] && node.assumptionType.equals(AssumptionType.Postcondition))) &&
        fullGraph.existsAnyDependency(Set(node.id), explicitAssertionNodeIds))

    val crucialNodes = nodesToAnalyze ++ dependencies
    val (newProgram, cleanseFactor) = cleanseProgram(program, crucialNodes)
    val result = frontend.verifier.verify(newProgram)
    val writer = new PrintWriter(exportFileName)
    writer.println("// test result: " + !result.isInstanceOf[verifier.Failure])
    writer.println("// cleanse factor: " + cleanseFactor)
    writer.println(newProgram.toString())
    writer.close()
    assert(!result.isInstanceOf[verifier.Failure], s"Failed to verify new program ${newProgram.toString()}")
  }

  private def cleanseProgram(program: Program, crucialNodes: Set[AssumptionAnalysisNode]): (ast.Program, Double) = {
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
        removed += (pres.size-newPres.size) + (posts.size-newPosts.size)
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
        removed += 1 + (invs.size-newInvs.size)
        ast.Seqn(Seq(
          ast.LocalVarDeclStmt(ast.LocalVarDecl("nonDetermBool", ast.Bool)())(),
          ast.While(ast.LocalVar("nonDetermBool", ast.Bool)(), newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT))
          , Seq())(whileStmt.pos, whileStmt.info, whileStmt.errT)
      case whileStmt@ast.While(cond, invs, body) =>
        val newInvs = invs filter (isCrucialExp(_, crucialNodesWithExpInfo))
        total += 1 + invs.size
        removed += (invs.size-newInvs.size)
        ast.While(cond, newInvs, body)(whileStmt.pos, whileStmt.info, whileStmt.errT)
      case s: Stmt if !isCrucialStmt(s, crucialNodesWithStmtInfo) =>
        total += 1
        removed += 1
        ast.Inhale(ast.TrueLit()())()
      case s: Stmt =>
        total += 1
        s
    }, Traverse.BottomUp).execute(program)
    (newProgram, removed.toDouble/total.toDouble)
  }

  private def isCrucialExp(exp: ast.Exp, crucialNodesWithExpInfo: Set[ExpAnalysisSourceInfo]): Boolean = {
    crucialNodesWithExpInfo exists(n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(exp.pos))) // TODO ake: currently we compare only lines not columns!
  }

  private def isCrucialStmt(stmt: ast.Stmt, crucialNodesWithStmtInfo: Set[StmtAnalysisSourceInfo]): Boolean = {
    crucialNodesWithStmtInfo exists(n => n.getPositionString.equals(AnalysisSourceInfo.extractPositionString(stmt.pos)))
  }
}
