
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.SiliconFrontend
import viper.silicon.assumptionAnalysis.{AssumptionAnalysisGraph, AssumptionAnalysisNode, AssumptionType, DependencyAnalysisReporter, GeneralAssumptionNode}
import viper.silver.ast.{AnnotationInfo, HasLineColumn, Infoed, NoPosition, Node, Position, Positioned, Program, Seqn, VirtualPosition}
import viper.silver.ast.utility.{DiskLoader, ViperStrategy}
import viper.silver.frontend.SilFrontend
import viper.silver.verifier

import java.io.File
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.IterableHasAsScala
import scala.util.{Failure, Success}


/**
 * Annotations
 * @dependency() -> for assumptions that should be reported as a dependency
 * @obsolete() -> for assumptions that should NOT be reported as a dependency
 * @testAssertion() -> the queried assertion
 *
 * assumptions/assertions that are not annotated are ignored
 *
 * !!! THERE CAN ONLY BE 1 TEST ASSERTION PER METHOD,
 * but multiple dependency/obsolete annotations are allowed
 *
 */
class AssumptionAnalysisTests extends AnyFunSuite {

  val CHECK_PRECISION = true

  val obsoleteKeyword = "obsolete"
  val dependencyKeyword = "dependency"

  val GENERATE_TESTS = false
  if(GENERATE_TESTS)
    generateTests("dependencyAnalysisTests/", "test-templates")


  val commandLineArguments: Seq[String] =
    Seq("--timeout", "100" /* seconds */, "--enableAssumptionAnalysis", "--z3Args", "proof=true unsat-core=true")


  val testDirectories: Seq[String] = Seq(
    "dependencyAnalysisTests/unitTests",
    "dependencyAnalysisTests/all",
  )
  testDirectories foreach createTests

//  test("dependencyAnalysisTests/all" + "/" + "imprecision"){
//    executeTest("dependencyAnalysisTests/all" + "/", "imprecision", frontend)
//  }


  def createTests(dirName: String): Unit = {
    val path = getClass.getClassLoader.getResource(dirName)
    val directoryStream = Files.newDirectoryStream(Paths.get(path.toURI)).asScala
    val dirContent = directoryStream.toList

    for (filePath: Path <- dirContent.sorted
         if Files.isReadable(filePath)
         if !Files.isDirectory(filePath)){
      val fileName = filePath.getFileName.toString.replace(".vpr", "")
      test(dirName + "/" + fileName){
        executeTest(dirName + "/", fileName, frontend)
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

    val program: Program = tests.loadProgram(filePrefix, fileName, frontend)
    val result = frontend.verifier.verify(program)

    assert(result match {
      case verifier.Success => true
      case verifier.Failure(_) => false
    }, s"Verification failed for ${filePrefix + fileName + ".vpr"}")

    val assumptionGraphsReal = frontend.reporter.asInstanceOf[DependencyAnalysisReporter].assumptionGraphs
    val stmtsWithAssumptionAnnotation: Set[Infoed] = extractAnnotatedAssumptionStmts(program)
    val allAssumptionNodes = assumptionGraphsReal.flatMap(_.nodes.filter(_.isInstanceOf[GeneralAssumptionNode]))

    // TODO ake: warning if testAssertion is missing
    var errorMsgs = stmtsWithAssumptionAnnotation.map(checkNodeExists(allAssumptionNodes, _)).filter(_.isDefined).map(_.get).toSeq
    errorMsgs ++= assumptionGraphsReal flatMap checkDependencies
    val warnMsgs = assumptionGraphsReal flatMap checkNonDependencies
    if(CHECK_PRECISION)
      errorMsgs ++= warnMsgs
    else if(warnMsgs.nonEmpty) println(warnMsgs.mkString("\n")) // TODO ake: warning

    val check = errorMsgs.isEmpty
    assert(check, "\n" + errorMsgs.mkString("\n"))
  }

  private def extractAnnotatedAssumptionStmts(program: Program): Set[Infoed] = {
    var nodesWithAnnotation: Set[Infoed] = Set.empty
    val newP: Program = ViperStrategy.Slim({
      case s: Seqn => s
      case n: Infoed =>
        val annotationInfo = n.info.getUniqueInfo[AnnotationInfo]
          .filter(ai => ai.values.contains(obsoleteKeyword) || ai.values.contains(dependencyKeyword))
        if (annotationInfo.isDefined)
          nodesWithAnnotation += n
        n
    }).execute(program)
    nodesWithAnnotation
  }

  private def checkNodeExists(analysisNodes: List[AssumptionAnalysisNode], node: Infoed): Option[String] = {
    val pos = extractSourceLine(node.asInstanceOf[Positioned].pos)
    val annotationInfo = node.info.getUniqueInfo[AnnotationInfo]
      .map(ai => ai.values.getOrElse(obsoleteKeyword, ai.values.getOrElse(dependencyKeyword, List.empty))).getOrElse(List.empty)
    val assumptionType = annotationInfo.map(AssumptionType.fromString).filter(_.isDefined).map(_.get)
    val nodeExists = analysisNodes exists (analysisNode => {
      extractSourceLine(analysisNode.sourceInfo.getPosition) == pos &&
        assumptionType.forall(_.equals(analysisNode.assumptionType))
    })
    Option.when(!nodeExists)(s"Missing analysis node:\n${node.toString}\n$pos")
  }

  def extractSourceLine(pos: Position): Int = {
    pos match {
      case column: HasLineColumn => column.line
      case _ => -1
    }
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
    val assumptionNodes = extractTestObsoleteAssumptionNodesFromGraph(assumptionGraph)
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
        node.sourceInfo.toString.contains("@testAssertion()")
    ).toSeq
  }

  def extractTestAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node => {
      (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale")) &&
        !node.assumptionType.equals(AssumptionType.Internal) && // TODO ake: really?
        node.sourceInfo.toString.contains("@" + dependencyKeyword + "()")
    }
    ).toSeq
  }

  def extractTestObsoleteAssumptionNodesFromGraph(graph: AssumptionAnalysisGraph): Seq[AssumptionAnalysisNode] = {
    graph.nodes.filter(node => {
      (node.getNodeType.equals("Assumption") || node.getNodeType.equals("Inhale")) &&
        !node.assumptionType.equals(AssumptionType.Internal) &&
        node.sourceInfo.toString.contains("@" + obsoleteKeyword + "()")
    }
    ).toSeq
  }
}
